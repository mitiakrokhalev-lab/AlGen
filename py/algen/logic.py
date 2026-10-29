"""Вывод по базе через SAT-решатель.

Правила базы — клаузы «посылки ⇒ вывод» над сценой ролей. Здесь каждое
правило ЗАЗЕМЛЯЕТСЯ на граф условия: роли пробегают все термы подходящего сорта
с согласованными связями (ambient, dom, cod), образцы вроде Z(X) или X/N
становятся конкретными термами. Получается пропозициональная формула, и
вопрос «следует ли цель из посылок» решается SAT-решателем.

Чем это лучше прямого вывода по Хорну, которым работал старый движок:

* контрапозиция и разбор случаев получаются сами: решатель проверяет все
  миры, а не идёт вперёд от посылок;
* решатель отдаёт ЯДРО — те посылки, без которых вывод не проходит. Если ядро
  меньше набора посылок, условие задачи ослабляется, и задача в выдачу не
  идёт: это первый признак тривиальности из определения пользователя;
* противоречивость условия видна той же проверкой.

Частичные конструкции (фактор берётся только по нормальной подгруппе)
учитываются так: в каждую клаузу, где встречается такой терм, условие
существования терма входит дополнительной посылкой.
"""

import itertools
import json
from dataclasses import dataclass, field
from pathlib import Path

from pysat.solvers import Solver

LINKS = ("ambient", "dom", "cod", "base")
DATA = Path(__file__).resolve().parents[2] / "data"


# --- словарь -----------------------------------------------------------------


class Vocab:
    """Словарь раздела: сорта, свойства, конструкции, вырождения, правила.

    Берётся из выгрузки `node tools/dump-rules.mjs <раздел>`.
    """

    def __init__(self, d):
        self.id = d["id"]
        self.up = {}
        for lo, hi in d["subsorts"]:
            self.up.setdefault(lo, {lo}).add(hi)
        self.props = {p["id"]: (p["sort"] if isinstance(p["sort"], list) else [p["sort"]])
                      for p in d["properties"]}
        self.rels = {r["id"]: r for r in d["relations"]}
        self.cons = {c["id"]: c for c in d["constructions"]}
        self.degen = d["degenerations"]
        self.rules = [r for r in d["rules"]]
        for c in d.get("gives", []):
            scene = [{"name": s["role"], "sort": s["sort"],
                      **{k: s[k] for k in LINKS if k in s}} for s in c["in"]]
            t = {"op": c["op"], "args": [s["role"] for s in c["in"]]}
            for p, v in c["gives"].items():
                self.rules.append({"id": f"{c['op']}:даёт:{p}", "scene": scene, "if": [],
                                   "then": {"p": p, "t": t, "значение": v}})

    @classmethod
    def section(cls, name):
        """Словарь раздела из репозитория: data/vocab/<раздел>.json с поправками
        data/new/<раздел>.json. Выгрузка обновляется командой
        `node tools/dump-rules.mjs <раздел> > data/vocab/<раздел>.json`."""
        patch = DATA / "new" / f"{name}.json"
        return cls.load(DATA / "vocab" / f"{name}.json", patch if patch.exists() else None)

    @classmethod
    def load(cls, path, patch=None):
        """Выгрузка словаря и, если есть, поправки data/new/<раздел>.json."""
        with open(path, encoding="utf-8") as f:
            v = cls(json.load(f))
        if patch is not None:
            with open(patch, encoding="utf-8") as f:
                v.apply(json.load(f))
        return v

    def apply(self, patch):
        for p in patch.get("свойства", []):
            if p["id"] in self.props:
                raise KeyError(f"свойство {p['id']} уже есть в словаре")
            self.props[p["id"]] = p["sort"] if isinstance(p["sort"], list) else [p["sort"]]
        drop = {x["id"] for x in patch.get("снять", [])}
        missing = drop - {r["id"] for r in self.rules}
        if missing:
            raise KeyError(f"снимаемых правил нет в базе: {sorted(missing)}")
        added = []
        for r in patch.get("добавить", []):
            scene = r["scene"]
            if isinstance(scene, dict):  # запись базы: {"N": {"sort": …, "ambient": "X"}}
                scene = [{"name": k, "sort": v} if isinstance(v, str) else {"name": k, **v}
                         for k, v in scene.items()]
            added.append({**r, "scene": scene})
        self.rules = [r for r in self.rules if r["id"] not in drop] + added
        # Равенства конструкций (как «вырождения» словаря): «Gᵃᵇ = G/G′».
        self.degen = self.degen + patch.get("вырождения", [])
        # Новые конструкции (например, сплетение); «gives» — как в словаре.
        for c in patch.get("конструкции", []):
            if c["id"] in self.cons:
                raise KeyError(f"конструкция {c['id']} уже есть в словаре")
            self.cons[c["id"]] = c
            scene = [{"name": x["role"], "sort": x["sort"], **{k: x[k] for k in LINKS if k in x}} for x in c["in"]]
            t = {"op": c["id"], "args": [x["role"] for x in c["in"]]}
            for p, v in (c.get("gives") or {}).items():
                self.rules.append({"id": f"{c['id']}:даёт:{p}", "scene": scene, "if": [],
                                   "then": {"p": p, "t": t, "значение": v}})

    def fits(self, have, want):
        return have == want or want in self.up.get(have, ())

    def prop_fits(self, p, sort):
        return any(self.fits(sort, s) for s in self.props.get(p, ()))


# --- граф условия ------------------------------------------------------------


@dataclass(frozen=True)
class Var:
    """Свободная вершина условия: «пусть G — группа», «пусть N ⩽ G»."""

    name: str

    def __str__(self):
        return self.name

    def __hash__(self):  # кэш: термы — ключи словарей в горячих циклах
        h = self.__dict__.get("_h")
        if h is None:
            h = hash(("Var", self.name))
            object.__setattr__(self, "_h", h)
        return h

    def __getstate__(self):  # хэш строк зависит от процесса: кэш не сохраняем
        return {k: v for k, v in self.__dict__.items() if k != "_h"}

    def __setstate__(self, st):
        for k, v in st.items():
            object.__setattr__(self, k, v)


@dataclass(frozen=True)
class App:
    """Построенный терм: конструкция над термами."""

    op: str
    args: tuple

    def __hash__(self):
        h = self.__dict__.get("_h")
        if h is None:
            h = hash((self.op, self.args))
            object.__setattr__(self, "_h", h)
        return h

    def __getstate__(self):  # хэш строк зависит от процесса: кэш не сохраняем
        return {k: v for k, v in self.__dict__.items() if k != "_h"}

    def __setstate__(self, st):
        for k, v in st.items():
            object.__setattr__(self, k, v)

    def __str__(self):
        return f"{self.op}({', '.join(map(str, self.args))})"


@dataclass
class Info:
    sort: str
    links: dict = field(default_factory=dict)
    depth: int = 0  # сколько построений над исходными вершинами условия


class Graph:
    """Термы условия с сортами и связями.

    Исходные вершины (и построенные термы, названные в условии) имеют глубину
    0. При заземлении правил граф ДОСТРАИВАЕТСЯ термами, которых в условии нет,
    но которые нужны доказательству («эпиморфный образ абелевой абелев»
    требует im φ). Глубина достройки ограничена параметром grow.
    """

    def __init__(self, vocab):
        self.v = vocab
        self.terms = {}

    def var(self, name, sort, **links):
        t = Var(name)
        for k, s in links.items():
            if s not in self.terms:
                raise KeyError(f"{name}: связь {k} на неизвестный терм {s}")
        self.terms[t] = Info(sort, dict(links))
        return t

    def _ref(self, expr, env):
        """Ссылка конструкции: 'X', 'dom F', 'base dom F' или образец терма."""
        if isinstance(expr, dict):
            return self.make(expr["op"], [self._ref(a, env) for a in expr.get("args", [])])
        parts = str(expr).split()
        t = env[parts[-1]]
        for rel in reversed(parts[:-1]):
            if t is None:
                return None
            t = self.terms[t].links.get(rel)
        return t

    def make(self, op, args, depth_limit=None):
        """Терм op(args) или None, если связи слотов не согласованы."""
        c = self.v.cons.get(op)
        if c is None or len(c["in"]) != len(args) or any(a is None for a in args):
            return None
        t = App(op, tuple(args))
        if t in self.terms:
            return t
        env = {}
        for slot, a in zip(c["in"], args):
            info = self.terms.get(a)
            if info is None or not self.v.fits(info.sort, slot["sort"]):
                return None
            env[slot["role"]] = a
        for slot, a in zip(c["in"], args):
            for k in LINKS:
                if k in slot and self.terms[a].links.get(k) != self._ref(slot[k], env):
                    return None
        depth = 1 + max((self.terms[a].depth for a in args), default=0)
        if depth_limit is not None and depth > depth_limit:
            return None
        out = c["out"] if isinstance(c["out"], dict) else {"sort": c["out"]}
        links = {}
        for k in LINKS:
            if k in out:
                r = self._ref(out[k], env)
                if r is None:
                    return None
                links[k] = r
        self.terms[t] = Info(out["sort"], links, depth)
        return t

    def given(self, t):
        """Пометить построенный терм как часть условия (глубина 0)."""
        self.terms[t].depth = 0
        return t

    def requires(self, t):
        """Условия существования терма: [(свойство, терм)], рекурсивно."""
        out = []
        if isinstance(t, App):
            c = self.v.cons[t.op]
            for slot, a in zip(c["in"], t.args):
                for p in slot.get("requires", []):
                    out.append((p, a))
                out += self.requires(a)
        return out


# --- заземление --------------------------------------------------------------


class Theory:
    """Пропозициональная теория графа: переменные-атомы и клаузы."""

    def __init__(self, graph, grow=1, extra=()):
        self.g = graph
        self.v = graph.v
        self.grow = grow
        self.var = {}
        self.atoms = []
        self.clauses = []
        self.origin = []  # id правила для каждой клаузы
        for a in extra:  # атомы перебора (отношения), которым нужны аксиомы равенства
            self.lit(a)
        self._build()

    # атомы ---------------------------------------------------------------

    def lit(self, atom, value=True):
        if atom[0] == "r" and atom[1] in ("iso", "eq-sub") and str(atom[3]) < str(atom[2]):
            atom = (atom[0], atom[1], atom[3], atom[2])  # симметричные отношения
        if atom[0] == "r" and atom[1] in ("iso", "eq-sub") and atom[2] == atom[3]:
            return None if value else False  # t ≅ t верно всегда
        if atom not in self.var:
            self.var[atom] = len(self.atoms) + 1
            self.atoms.append(atom)
        n = self.var[atom]
        return n if value else -n

    # заземление правил ----------------------------------------------------

    def _bindings(self, scene):
        roles = sorted(scene, key=lambda r: sum(1 for k in LINKS if k in r))
        names = {r["name"] for r in roles}
        for r in roles:
            for k in LINKS:
                if k in r and r[k].split()[-1] not in names:
                    return
        terms = list(self.g.terms.items())

        def go(i, env):
            if i == len(roles):
                yield dict(env)
                return
            r = roles[i]
            for t, info in terms:
                if not self.v.fits(info.sort, r["sort"]):
                    continue
                ok = True
                for k in LINKS:
                    if k in r:
                        want = self.g._ref(r[k], env)
                        if want is None or info.links.get(k) != want:
                            ok = False
                            break
                if ok:
                    env[r["name"]] = t
                    yield from go(i + 1, env)
                    del env[r["name"]]

        yield from go(0, {})

    def _term(self, pat, env, limit):
        if isinstance(pat, str):
            return env.get(pat)
        if "bind" in pat:
            return None
        args = [self._term(a, env, limit) for a in pat.get("args", [])]
        if any(a is None for a in args):
            return None
        return self.g.make(pat["op"], args, depth_limit=limit)

    def _atom(self, a, env, limit):
        """(атом, значение, термы) или None, если терм не строится."""
        if "rel" in a:
            ts = [self._term(x, env, limit) for x in a["args"]]
            if any(t is None for t in ts):
                return None
            return ("r", a["rel"], *ts), a.get("значение", True), ts
        t = self._term(a["t"], env, limit)
        if t is None or not self.v.prop_fits(a["p"], self.g.terms[t].sort):
            return None
        return ("p", a["p"], t), a.get("значение", True), [t]

    def _ground_rule(self, r, limit):
        """(посылки, выводы): вывод правила — атом или {"или": [атомы]}."""
        concl = r["then"]["или"] if "или" in r["then"] else [r["then"]]
        for env in self._bindings(r["scene"]):
            prem = [self._atom(a, env, limit) for a in r["if"]]
            outs = [self._atom(a, env, limit) for a in concl]
            if any(p is None for p in prem + outs):
                continue
            yield prem, outs

    def _add(self, lits, origin):
        if any(l is None for l in lits):
            return  # в клаузе тождественно истинный литерал
        lits = [l for l in lits if l is not False]
        self.clauses.append(lits)
        self.origin.append(origin)

    def _clause(self, parts, origin):
        """Посылки ⇒ вывод (или дизъюнкция выводов), плюс условия существования термов."""
        prem, outs = parts
        lits = []
        terms = [t for _, _, ts in prem + outs for t in ts]
        for p, t in {x for t in terms for x in self.g.requires(t)}:
            lits.append(self.lit(("p", p, t), False))
        for atom, val, _ in prem:
            l = self.lit(atom, val)
            if l is None:  # посылка t ≅ t истинна, из клаузы выпадает
                continue
            lits.append(-l if l is not False else None)
        for atom, val, _ in outs:
            lits.append(self.lit(atom, val))
        self._add(lits, origin)

    def _build(self):
        # Достройка: сначала растим граф образцами правил до глубины grow,
        # затем заземляем всё на получившемся графе без роста.
        for _ in range(self.grow):
            before = len(self.g.terms)
            for r in self.v.rules:
                list(self._ground_rule(r, self.grow))
            for d in self.v.degen:
                list(self._degen(d, self.grow))
            if len(self.g.terms) == before:
                break
        limit = max(i.depth for i in self.g.terms.values())
        for r in self.v.rules:
            for parts in self._ground_rule(r, limit):
                self._clause(parts, r["id"])
        for d in self.v.degen:
            for cond, t, s in self._degen(d, limit):
                self._equal(cond, t, s, f"вырождение {d['op']}: {d.get('почему', '')}")
        self._equality_axioms()

    # вырождения и равенства ----------------------------------------------

    def _degen(self, d, limit):
        """(условие, t, s): при условии терм t равен терму s."""
        c = self.v.cons.get(d["op"])
        if c is None:
            return
        roles = [s["role"] for s in c["in"]]
        for t in [t for t in self.g.terms if isinstance(t, App) and t.op == d["op"]]:
            env = dict(zip(roles, t.args))
            ok = True
            for role, pat in d.get("pattern", {}).items():
                a = env.get(role)
                if not isinstance(a, App) or a.op != pat["op"]:
                    ok = False
                    break
                if "bind" in pat:
                    env.update(zip(pat["bind"], a.args))
                elif self._term(pat, env, limit) != a:
                    ok = False
                    break
            if not ok:
                continue
            cond = [("p", p, env[role], v) for role, ps in d.get("when", {}).items()
                    for p, v in ps.items() if role in env]
            eq = d["equals"]
            s = env.get(eq) if isinstance(eq, str) else self._term(eq, env, limit)
            if s is not None and s != t:
                yield cond, t, s

    def _equal(self, cond, t, s, origin):
        st, ss = self.g.terms[t].sort, self.g.terms[s].sort
        rel = "eq-sub" if st == ss and st.endswith(".sub") else "iso"
        if rel == "iso" and not (self.v.fits(st, "Grp.obj") and self.v.fits(ss, "Grp.obj")):
            return
        lits = [self.lit(("p", p, x), False) for p, x in {x for y in (t, s) for x in self.g.requires(y)}]
        lits += [self.lit(("p", p, x), not v) for _, p, x, v in cond]
        lits.append(self.lit(("r", rel, t, s)))
        self._add(lits, origin)

    def _equality_axioms(self):
        """≅ и = на термах: перенос свойств, симметрия уже в записи, транзитивность."""
        pairs = [a for a in self.atoms if a[0] == "r" and a[1] in ("iso", "eq-sub")]
        props = {}
        for a in self.atoms:
            if a[0] == "p":
                props.setdefault(a[2], set()).add(a[1])
        # ≅ переносит только свойства, объявленные на сорте объекта (или выше):
        # «N нормальна в G» — свойство вложения, и изоморфная N группа его не
        # наследует.
        obj_sort = self.v.rels["iso"]["in"][0] if "iso" in self.v.rels else None
        obj_props = {p for p, sorts in self.v.props.items()
                     if obj_sort and any(self.v.fits(obj_sort, s) for s in sorts)}
        for _, rel, a, b in pairs:
            e = self.var[("r", rel, a, b)]
            ps = props.get(a, set()) | props.get(b, set())
            for p in ps:
                if rel == "iso" and p not in obj_props:
                    continue
                if not (self.v.prop_fits(p, self.g.terms[a].sort) and self.v.prop_fits(p, self.g.terms[b].sort)):
                    continue
                pa, pb = self.lit(("p", p, a)), self.lit(("p", p, b))
                self._add([-e, -pa, pb], f"{rel}: перенос {p}")
                self._add([-e, pa, -pb], f"{rel}: перенос {p}")
        by_rel = {}
        for _, rel, a, b in pairs:
            by_rel.setdefault(rel, set()).add((a, b))
        for rel, ps in by_rel.items():
            nodes = {x for p in ps for x in p}
            if len(nodes) > 40:
                continue
            for a, b, c in itertools.permutations(nodes, 3):
                ab, bc, ac = (self.lit(("r", rel, *sorted((a, b), key=str))),
                              self.lit(("r", rel, *sorted((b, c), key=str))),
                              self.lit(("r", rel, *sorted((a, c), key=str))))
                if None in (ab, bc, ac):
                    continue
                self._add([-ab, -bc, ac], f"{rel}: транзитивность")

    # вопросы --------------------------------------------------------------

    def solver(self):
        s = Solver(name="g4", bootstrap_with=self.clauses)
        return s


@dataclass
class Verdict:
    kind: str           # выводится | опровергается | противоречие | неизвестно
    core: list = None   # посылки, которых достаточно (для «выводится», «опровергается», «противоречие»)


def decide(theory, premises, goal, solver=None):
    """premises, goal: (атом, значение). Атом ('p', свойство, терм) или ('r', …)."""
    own = solver is None
    s = solver or theory.solver()
    try:
        assume = {}
        for a, v in premises:
            l = theory.lit(a, v)
            if l is None:
                continue
            if l is False:
                return Verdict("противоречие", [(a, v)])
            assume[l] = (a, v)
        lits = list(assume)
        if not s.solve(assumptions=lits):
            return Verdict("противоречие", [assume[l] for l in s.get_core() or []])
        g = theory.lit(*goal)
        if g is None:
            return Verdict("выводится", [])
        if g is False:
            return Verdict("опровергается", [])
        if not s.solve(assumptions=lits + [-g]):
            return Verdict("выводится", [assume[l] for l in s.get_core() or [] if l in assume])
        if not s.solve(assumptions=lits + [g]):
            return Verdict("опровергается", [assume[l] for l in s.get_core() or [] if l in assume])
        return Verdict("неизвестно")
    finally:
        if own:
            s.delete()
