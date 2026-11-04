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



# Мера размера (algen.table, ALGEN_SIZE): правило с несколькими термами вселенной
# заземляется только на термах, которые встречаются вместе хотя бы в одной схеме базы.
# Термы вне вселенной (достроенные теорией) и переменные — без ограничений. Вывод
# остаётся верным; теряются лишь выводы через термы чужих схем.
PAIR_FILTER = None   # множество frozenset({str, str})
PAIR_UNI = None      # строки термов вселенной
_STR = {}


def _s(t):
    s = _STR.get(t)
    if s is None:
        s = _STR[t] = str(t)
    return s


_NEIGH = {}


def _neighbours():
    """Соседи терма вселенной по фильтру пар: {строка: множество строк}."""
    if _NEIGH.get("obj") is not PAIR_FILTER:
        nb = {}
        for p in PAIR_FILTER:
            a, b = tuple(p) if len(p) == 2 else (next(iter(p)),) * 2
            nb.setdefault(a, set()).add(b)
            nb.setdefault(b, set()).add(a)
        _NEIGH.clear()
        _NEIGH.update(obj=PAIR_FILTER, nb=nb)
    return _NEIGH["nb"]


def _pair_ok(t, env):
    s = _STR.get(t)
    if s is None:
        s = _STR[t] = str(t)
    if s not in PAIR_UNI:
        return True
    for u in env.values():
        su = _STR.get(u)
        if su is None:
            su = _STR[u] = str(u)
        if su != s and su in PAIR_UNI and frozenset((s, su)) not in PAIR_FILTER:
            return False
    return True

class ClauseStore:
    """Клаузы теории в плоском массиве int32 с границами (int64) вместо списка
    списков: у баз с тремя переменными десятки миллионов клауз, а список из трёх
    больших int в Python — ≈ 160 байт (каркасы GE и GN падали по памяти на 16 ГБ).
    Те же клаузы в том же порядке: перебор отдаёт списки, как прежде."""
    __slots__ = ("data", "offs")

    def __init__(self, clauses=()):
        from array import array
        self.data, self.offs = array("i"), array("q", [0])
        for c in clauses:
            self.append(c)

    def append(self, lits):
        self.data.extend(lits)
        self.offs.append(len(self.data))

    def __len__(self):
        return len(self.offs) - 1

    def __iter__(self):
        d, o = self.data, self.offs
        for i in range(len(o) - 1):
            yield d[o[i]:o[i + 1]].tolist()

    def __getitem__(self, i):
        if isinstance(i, slice):
            return [self[j] for j in range(*i.indices(len(self)))]
        if i < 0:
            i += len(self)
        if not 0 <= i < len(self):
            raise IndexError(i)
        return self.data[self.offs[i]:self.offs[i + 1]].tolist()


class OriginStore:
    """id правила для каждой клаузы: номер в списке имён (массив) вместо ссылки."""
    __slots__ = ("names", "index", "ids")

    def __init__(self):
        from array import array
        self.names, self.index, self.ids = [], {}, array("I")

    def append(self, name):
        k = self.index.get(name)
        if k is None:
            k = self.index[name] = len(self.names)
            self.names.append(name)
        self.ids.append(k)

    def __len__(self):
        return len(self.ids)

    def __getitem__(self, i):
        return self.names[self.ids[i]]

    def __iter__(self):
        return (self.names[k] for k in self.ids)


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
        self.quantified = {}
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
        # правила «X:даёт:p» строятся из конструкций и могут быть не построены (check_rules)
        missing = {x for x in drop - {r["id"] for r in self.rules} if ":даёт:" not in x and ":сохраняет:" not in x}
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
        # Новые отношения (например, вложение A ↪ B).
        for r in patch.get("отношения", []):
            if r["id"] in self.rels:
                raise KeyError(f"отношение {r['id']} уже есть в словаре")
            self.rels[r["id"]] = r
        # Свойства с квантором по подгруппам: Q(G) ⇔ ∀ H ⩽ G (фильтр(H) ⇒ P(H)).
        for q in patch.get("кванторные", []):
            self._quantified(q)
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
            # «preserves»: свойство всех аргументов-подгрупп переходит к результату
            subs = [x["role"] for x in c["in"] if x["sort"] == "Grp.sub"]
            for p in c.get("preserves") or []:
                self.rules.append({"id": f"{c['id']}:сохраняет:{p}", "scene": scene,
                                   "if": [{"p": p, "t": r} for r in subs], "then": {"p": p, "t": t}})

    def _quantified(self, q):
        """Свойство «всякая подгруппа H с фильтром обладает P» (локально конечна,
        все собственные подгруппы абелевы, …) и его правила:
          исключение  Q(G), H ⩽ G, фильтр(H) ⇒ P(H);
          на себя     Q(G), фильтр(G) ⇒ P(G) (если фильтр не требует H ≠ G);
          наследование Q(G), H ⩽ G ⇒ Q(H) («наследуется»: фильтр в H влечёт фильтр в G);
          введение    P(G) ⇒ Q(G) («из p»: P наследуется подгруппами)."""
        qid, p, filt = q["id"], q["p"], q.get("фильтр", [])
        if qid in self.props:
            raise KeyError(f"свойство {qid} уже есть в словаре")
        self.props[qid] = ["Grp.obj"]
        X = {"name": "X", "sort": "Grp.obj"}
        H = {"name": "H", "sort": "Grp.sub", "ambient": "X"}

        def lit(x, t):
            return {"p": x["p"], "t": t, **({"значение": False} if x.get("значение") is False else {})}
        self.rules.append({"id": f"{qid}:исключение", "scene": [X, H],
                           "if": [{"p": qid, "t": "X"}] + [lit(x, "H") for x in filt],
                           "then": {"p": p, "t": "H"}})
        if not any(x["p"] == "whole" for x in filt):
            self.rules.append({"id": f"{qid}:на себя", "scene": [X],
                               "if": [{"p": qid, "t": "X"}] + [lit(x, "X") for x in filt],
                               "then": {"p": p, "t": "X"}})
        if q.get("наследуется"):
            self.rules.append({"id": f"{qid}:наследуется", "scene": [X, H],
                               "if": [{"p": qid, "t": "X"}], "then": {"p": qid, "t": "H"}})
        if q.get("из p"):
            self.rules.append({"id": f"{qid}:из {p}", "scene": [X],
                               "if": [{"p": p, "t": "X"}], "then": {"p": qid, "t": "X"}})
        self.quantified = getattr(self, "quantified", {})
        self.quantified[qid] = q

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
        return {k: v for k, v in self.__dict__.items() if k not in ("_h", "_s")}

    def __setstate__(self, st):
        for k, v in st.items():
            object.__setattr__(self, k, v)

    def __str__(self):
        # имя терма запоминается: таблица сортирует пары термов по имени на каждой строке
        s = self.__dict__.get("_s")
        if s is None:
            s = f"{self.op}({', '.join(map(str, self.args))})"
            object.__setattr__(self, "_s", s)
        return s


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
        memo = self.__dict__.setdefault("_req", {})
        if t not in memo:
            memo[t] = self._requires(t)
        return memo[t]

    def _requires(self, t):
        out = []
        if isinstance(t, App):
            c = self.v.cons[t.op]
            for slot, a in zip(c["in"], t.args):
                for p in slot.get("requires", []):
                    out.append((p, a))
                out += self.requires(a)
        return out


# --- заземление --------------------------------------------------------------


# Симметричные отношения: атом — с аргументами по возрастанию строки;
# рефлексивные: R(t, t) верно всегда.
SYMMETRIC = {"iso", "eq-sub", "conj-sub", "permutes", "commute", "conjugate", "eq-elt", "num-eq", "num-coprime"}
REFLEXIVE = SYMMETRIC - {"num-coprime"}


class Theory:
    """Пропозициональная теория графа: переменные-атомы и клаузы."""

    def __init__(self, graph, grow=1, extra=(), grow_ops=None):
        self.g = graph
        self.grow_ops = grow_ops  # какие конструкции можно достраивать (None — все)
        self.v = graph.v
        self.grow = grow
        self.var = {}
        self._lc = {}  # кэш lit: атом → номер переменной (0 — тождественно верный)
        self.atoms = []
        self.clauses = ClauseStore()
        self.origin = OriginStore()  # id правила для каждой клаузы
        for a in extra:  # атомы перебора (отношения), которым нужны аксиомы равенства
            self.lit(a)
        self._build()

    # атомы ---------------------------------------------------------------

    def lit(self, atom, value=True):
        n = self._lc.get(atom)
        if n is None:
            n = self._lc[atom] = self._var_of(atom)
        if n == 0:
            return None if value else False  # t ≅ t верно всегда
        return n if value else -n

    def _var_of(self, atom):
        if atom[0] == "r" and atom[1] in SYMMETRIC and str(atom[3]) < str(atom[2]):
            atom = (atom[0], atom[1], atom[3], atom[2])  # симметричные отношения
        if atom[0] == "r" and atom[1] in REFLEXIVE and atom[2] == atom[3]:
            return 0
        if atom not in self.var:
            self.var[atom] = len(self.atoms) + 1
            self.atoms.append(atom)
        return self.var[atom]

    # заземление правил ----------------------------------------------------

    def _bindings(self, scene, pats=(), shallow=(), limit=None):
        """Подстановки термов графа в роли сцены. pats — образцы термов правила
        ({"op", "args"}): если задать, роли из аргументов образца берутся из уже
        построенных термов с этой конструкцией (для заземления без роста:
        подстановка, при которой образца нет в графе, всё равно отбрасывается)."""
        roles = sorted(scene, key=lambda r: sum(1 for k in LINKS if k in r))
        names = {r["name"] for r in roles}
        def link_roles(x):
            if isinstance(x, dict):
                return set().union(*[link_roles(a) for a in x.get("args", [])]) if x.get("args") else set()
            return {x.split()[-1]}

        def ref(x, env):
            """Связь роли: как Graph._ref, но образец-терм только ищется, не строится."""
            if isinstance(x, dict):
                args = [ref(a, env) for a in x.get("args", [])]
                if any(a is None for a in args):
                    return None
                t = App(x["op"], tuple(args))
                return t if t in self.g.terms else None
            return self.g._ref(x, env)

        for r in roles:
            for k in LINKS:
                if k in r and not link_roles(r[k]) <= names:
                    return
        terms = list(self.g.terms.items())
        by_sort, by_link, pf_cache = {}, {}, {}

        def cands(r, env):
            lst = by_sort.get(r["sort"])
            if lst is None:
                lst = by_sort[r["sort"]] = [(t, i) for t, i in terms if self.v.fits(i.sort, r["sort"])]
            lkey = ("s", r["sort"])
            # связь на уже выбранную роль: только термы с этой связью (индекс)
            for k in LINKS:
                if k in r:
                    try:
                        want = ref(r[k], env)
                    except KeyError:
                        continue
                    idx = by_link.get((r["sort"], k))
                    if idx is None:
                        idx = by_link[r["sort"], k] = {}
                        for t, i in lst:
                            idx.setdefault(i.links.get(k), []).append((t, i))
                    lst = idx.get(want, [])
                    lkey = ("l", r["sort"], k, want)
                    break
            if r["name"] in shallow:
                # аргумент образца: новый терм глубины ⩽ limit строится только
                # из термов глубины < limit
                return [(t, i) for t, i in lst if i.depth < limit]
            if lkey[0] == "l":
                ok = allowed.get(r["name"])  # короткий список по связи: фильтр без кэша
                return lst if ok is None else [(t, i) for t, i in lst if t in ok]
            lst = restrict(r["name"], lst)
            # Фильтр пар: только соседи уже выбранного терма вселенной (подпоследовательность
            # в том же порядке; go всё равно проверяет _pair_ok, подстановки те же). Без него
            # правила о парах (⩽ антисимметрично) перебирают все пары термов сорта. Кэш —
            # только для списков по сорту: их немного, память ≈ размер фильтра пар.
            if PAIR_FILTER is not None and env:
                su = next((x for x in map(_s, env.values()) if x in PAIR_UNI), None)
                if su is not None:
                    # индекс списка (один на сорт и роль): место терма по имени и места
                    # термов вне вселенной; соседи su берутся по индексу, без кэша на su
                    key = (r["sort"], r["name"])
                    ix = pf_cache.get(key)
                    if ix is None or ix[0] is not lst:
                        pos = {_s(t): k for k, (t, _) in enumerate(lst)}
                        ix = pf_cache[key] = (lst, pos, [k for k, (t, _) in enumerate(lst) if _s(t) not in PAIR_UNI])
                    _, pos, outside = ix
                    nb = _neighbours().get(su, ())
                    if len(nb) > len(lst):  # список короче соседей — фильтр прямо по нему
                        lst = [(t, i) for t, i in lst if _s(t) not in PAIR_UNI or _s(t) == su or _s(t) in nb]
                    else:
                        ks = {pos[x] for x in nb if x in pos}
                        if su in pos:
                            ks.add(pos[su])
                        ks.update(outside)
                        lst = [lst[k] for k in sorted(ks)]
            return lst

        def fits(r, t, info, env):
            if not self.v.fits(info.sort, r["sort"]):
                return False
            for k in LINKS:
                if k in r:
                    want = ref(r[k], env)
                    if want is None or info.links.get(k) != want:
                        return False
            return True

        def go(i, env, order):
            if i == len(order):
                yield dict(env)
                return
            r = order[i]
            name = r["name"]
            if name in env:
                t = env[name]
                info = self.g.terms[t]
                added = derive(name, info, env)
                if added is not None:
                    # роль, выведенная из связи другой роли, проверяется на пары здесь —
                    # как проверялась бы при обычном переборе
                    if fits(r, t, info, env) and (name not in derived or PAIR_FILTER is None or _pair_ok(t, env)):
                        yield from go(i + 1, env, order)
                    for v in added:
                        del env[v]
                        derived.discard(v)
                return
            for t, info in cands(r, env):
                added = derive(name, info, env)
                if added is None:
                    continue
                if fits(r, t, info, env) and (PAIR_FILTER is None or _pair_ok(t, env)):
                    env[name] = t
                    yield from go(i + 1, env, order)
                    del env[name]
                for v in added:
                    del env[v]
                    derived.discard(v)

        # Роль со связями только на роли сцены (F : Mor(X, Y), N : Sub(X)) задаёт эти
        # роли своими связями: перебираем её первой, а X, Y берём из связей. Иначе
        # перебор шёл по всем парам групп X, Y и почти все отбрасывал (правила
        # «образ наследует P» — по 170 с на G и по 3 клаузы). Подстановки — те же.
        plain = lambda x: isinstance(x, str) and " " not in x and x in names

        def unifiable(x):
            # связь — роль сцены или образец из ролей (H : Sub(A ∗ B)): по терму
            # связи роли образца восстанавливаются однозначно
            if isinstance(x, dict):
                return "op" in x and "bind" not in x and bool(x.get("args")) and all(map(unifiable, x["args"]))
            return plain(x)

        det = {}
        for r in roles:
            ks = [k for k in LINKS if k in r]
            if ks and all(unifiable(r[k]) for k in ks):
                det[r["name"]] = [(k, r[k]) for k in ks]
        derived = set()

        def unify(x, t, env, added):
            """Связать роли образца x с термом t (False — не сходится)."""
            if t is None or t not in self.g.terms:
                return False
            if isinstance(x, dict):
                if not isinstance(t, App) or t.op != x["op"] or len(t.args) != len(x["args"]):
                    return False
                return all(unify(a, u, env, added) for a, u in zip(x["args"], t.args))
            if x in env:
                return env[x] == t
            env[x] = t
            derived.add(x)
            added.append(x)
            return True

        def derive(name, info, env):
            added = []
            for k, v in det.get(name, ()):
                if not unify(v, info.links.get(k), env, added):
                    for x in added:
                        del env[x]
                        derived.discard(x)
                    return None
            return added

        # Роль — аргумент образца правила (rank(X)): без терма-образца подстановка всё
        # равно отбрасывается, поэтому роль берётся только из аргументов уже
        # построенных термов с этой конструкцией (на этом месте). Подстановки те же.
        allowed = {}
        if pats:
            ops = self._by_op()

            def scan(x):
                if not isinstance(x, dict) or "op" not in x or "bind" in x:
                    return
                args = x.get("args", [])
                for i, a in enumerate(args):
                    if plain(a):
                        got = {t.args[i] for t in ops.get(x["op"], ()) if len(t.args) == len(args)}
                        allowed[a] = allowed[a] & got if a in allowed else got
                    else:
                        scan(a)

            for x in pats:
                scan(x)
        allow_cache = {}

        def restrict(name, lst):
            ok = allowed.get(name)
            if ok is None:
                return lst
            hit = allow_cache.get((id(lst), name))
            if hit is None or hit[0] is not lst:
                hit = allow_cache[id(lst), name] = (lst, [(t, i) for t, i in lst if t in ok])
            return hit[1]

        if det:
            roles = [r for r in roles if r["name"] in det] + [r for r in roles if r["name"] not in det]
        if allowed:
            free = [r for r in roles if r["name"] not in det and not any(k in r for k in LINKS)]
            rest = [r for r in roles if r not in free]
            free.sort(key=lambda r: len(allowed.get(r["name"], self.g.terms)))
            roles = [r for r in rest if r["name"] in det] + free + [r for r in rest if r["name"] not in det]

        # образец с наибольшим числом ролей среди аргументов
        best = None
        for pat in pats:
            args = pat.get("args", [])
            if "bind" in pat or not args or not all(isinstance(a, str) and a in names for a in args):
                continue
            if best is None or len(set(args)) > len(set(best["args"])):
                best = pat
        if best is None or len(set(best["args"])) < 2:
            # вложенный образец (Z(X ∗ Y)): подстановка без терма X ∗ Y всё равно
            # отбросится, поэтому роли берём из уже построенных термов X ∗ Y.
            # Роли образца проверяются на пары как выведенные — подстановки те же,
            # что у полного перебора.
            nest = None
            if pats:
                def subs(x):
                    if isinstance(x, dict) and "op" in x:
                        yield x
                        for a in x.get("args", []):
                            yield from subs(a)
                for top in pats:
                    for x in subs(top):
                        if unifiable(x):
                            n = len(self._pat_roles(x))
                            if n >= 2 and (nest is None or n > nest[0]):
                                nest = (n, x)
            if nest is None:
                yield from go(0, {}, roles)
                return
            for t in self._by_op().get(nest[1]["op"], ()):
                env, added = {}, []
                if unify(nest[1], t, env, added):
                    yield from go(0, env, roles)
                for x in added:
                    derived.discard(x)
            return
        for t in self._by_op().get(best["op"], ()):
            env = {}
            ok = True
            for a, x in zip(best["args"], t.args):
                if env.setdefault(a, x) != x:
                    ok = False
                    break
            if ok and len(t.args) == len(best["args"]):
                yield from go(0, env, roles)

    def _by_op(self):
        n = len(self.g.terms)
        if getattr(self, "_op_n", None) != n:
            idx = {}
            for t in self.g.terms:
                if isinstance(t, App):
                    idx.setdefault(t.op, []).append(t)
            self._op_idx, self._op_n = idx, n
        return self._op_idx

    @staticmethod
    def _all_patterns(r):
        """Все образцы-термы правила (верхнего уровня) по порядку, как их строит _atom."""
        out = []
        concl = r["then"]["или"] if "или" in r["then"] else [r["then"]]
        for a in list(r["if"]) + concl:
            for x in ([a["t"]] if "t" in a else a.get("args", [])):
                if isinstance(x, dict):
                    out.append(x)
        return out

    @staticmethod
    def _pat_roles(p):
        out = set()
        for a in p.get("args", []):
            if isinstance(a, str):
                out.add(a)
            elif isinstance(a, dict):
                out |= Theory._pat_roles(a)
        return out

    @staticmethod
    def _patterns(r):
        """Образцы-термы правила (dict с op) в посылках и выводах, без вложенных."""
        out = []
        concl = r["then"]["или"] if "или" in r["then"] else [r["then"]]
        for a in list(r["if"]) + concl:
            for x in ([a["t"]] if "t" in a else a.get("args", [])):
                if isinstance(x, dict) and "op" in x:
                    out.append(x)
        return out

    def _grow_term(self, pat, env):
        """Достройка: новый терм строится, только если среди его аргументов не
        больше одного построенного терма (Z(X/N), X × Z(X) — да; Z(X) × X′ — нет).
        Иначе граф большой схемы растёт квадратично, а такие термы выводу почти
        не нужны."""
        if isinstance(pat, str):
            return env.get(pat)
        if "bind" in pat:
            return None
        args = [self._grow_term(a, env) for a in pat.get("args", [])]
        if any(a is None for a in args):
            return None
        t = App(pat["op"], tuple(args))
        if t in self.g.terms:
            return t
        if sum(isinstance(a, App) for a in args) > 1:
            return None
        if self.grow_ops is not None and pat["op"] not in self.grow_ops:
            return None
        return self.g.make(pat["op"], args, depth_limit=self.grow)

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

    def _ground_rule(self, r, limit, grow=True):
        """(посылки, выводы): вывод правила — атом или {"или": [атомы]}.
        grow=False — без построения новых термов (все термы правила уже в графе)."""
        concl = r["then"]["или"] if "или" in r["then"] else [r["then"]]
        # «только заведённые»: отношения правила берутся только среди уже заведённых
        # атомов (столбцы таблицы и выводы прежних правил). Аксиомы вроде
        # транзитивности ⩽ на всех числовых термах иначе заводят атомы на все пары
        # и клаузы на все тройки (у G: 107³ ≈ 1,2 млн клауз на правило).
        known = r.get("только заведённые")
        envs = self._known_envs(r, concl) if known else None
        if envs is None:
            envs = self._bindings(r["scene"], () if grow else self._patterns(r))
        for env in envs:
            prem = []
            for a in r["if"]:
                x = self._atom(a, env, limit)
                if x is None or (known and x[0][0] == "r" and not self._known(x[0])):
                    break
                prem.append(x)
            else:
                outs = [self._atom(a, env, limit) for a in concl]
                if any(o is None or (known and o[0][0] == "r" and not self._known(o[0])) for o in outs):
                    continue
                yield prem, outs

    def _known_envs(self, r, concl):
        """Подстановки для правила «только заведённые»: соединение по уже заведённым
        атомам его отношений, без перебора всех пар и троек термов сцены. None —
        если какая-то роль сцены не входит в отношения (тогда обычный перебор)."""
        rels = [a for a in r["if"] + concl if "rel" in a]
        if not rels or not all(isinstance(x, str) for a in rels for x in a["args"]):
            return None
        sorts = {x["name"]: x["sort"] for x in r["scene"]}
        if not all(isinstance(v, str) for v in sorts.values()) or \
                set(sorts) - {x for a in rels for x in a["args"]}:
            return None
        idx = {}
        for a in self.atoms:
            if a[0] == "r" and any(a[1] == b["rel"] for b in rels):
                idx.setdefault(a[1], []).append(a[2:])
                if a[1] in SYMMETRIC:
                    idx[a[1]].append(a[2:][::-1])
        envs, bound = [{}], set()
        for a in sorted(rels, key=lambda a: len(idx.get(a["rel"], ()))):
            # соединение по хешу: кортежи атома — по значениям уже связанных ролей
            # (у всех подстановок шага они одни и те же); порядок тот же, что у
            # прежнего перебора всех кортежей, — без квадрата (⩽ антисимметрично)
            bpos = [i for i, x in enumerate(a["args"]) if x in bound]
            by_key = {}
            for tup in idx.get(a["rel"], ()):
                by_key.setdefault(tuple(tup[i] for i in bpos), []).append(tup)
            nxt = []
            for env in envs:
                for tup in by_key.get(tuple(env[a["args"][i]] for i in bpos), ()):
                    e = dict(env)
                    for x, t in zip(a["args"], tup):
                        if e.setdefault(x, t) != t or not self.v.fits(self.g.terms[t].sort, sorts[x]):
                            break
                    else:
                        nxt.append(e)
            envs = nxt
            bound |= set(a["args"])
            if not envs:
                break
        # роль сцены, встретившаяся дважды в одном атоме (m ⩽ m), уже отсеяна setdefault
        return envs

    def _known(self, atom):
        """Атом уже заведён (или тождественно верен) — без заведения нового."""
        if atom[0] == "r" and atom[1] in SYMMETRIC and str(atom[3]) < str(atom[2]):
            atom = (atom[0], atom[1], atom[3], atom[2])
        if atom[0] == "r" and atom[1] in REFLEXIVE and atom[2] == atom[3]:
            return True
        return atom in self.var

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
        for p, t in sorted({x for t in terms for x in self.g.requires(t)}, key=str):
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
            # Достройка создаёт только термы-образцы правил; правила с одинаковой
            # сценой и образцами (например, «× сохраняет P» для разных P)
            # строят одно и то же — их обходим один раз.
            seen = set()
            for r in self.v.rules:
                pats = self._all_patterns(r)
                if not pats:
                    continue
                key = json.dumps([r["scene"], pats], sort_keys=True, ensure_ascii=False)
                if key in seen:
                    continue
                seen.add(key)
                inner = {x for p in pats for x in self._pat_roles(p)}
                for env in self._bindings(r["scene"], (), shallow=inner, limit=self.grow):
                    for p in pats:
                        self._grow_term(p, env)
            for d in self.v.degen:
                list(self._degen(d, self.grow))
            if len(self.g.terms) == before:
                break
        limit = max(i.depth for i in self.g.terms.values())
        for r in self.v.rules:
            for parts in self._ground_rule(r, 0, grow=False):  # без новых термов
                self._clause(parts, r["id"])
        for d in self.v.degen:
            for cond, t, s in self._degen(d, limit):
                self._equal(cond, t, s, f"вырождение {d['op']}: {d.get('почему', '')}")
        self._equality_axioms()
        self._embeds_axioms()

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
        lits = [self.lit(("p", p, x), False) for p, x in sorted({x for y in (t, s) for x in self.g.requires(y)}, key=str)]
        lits += [self.lit(("p", p, x), not v) for _, p, x, v in cond]
        lits.append(self.lit(("r", rel, t, s)))
        self._add(lits, origin)

    # свойства, которые наследует подгруппа (и потому всякая вложимая группа)
    SUB_CLOSED = ("trivial", "abelian", "cyclic", "finite", "solvable", "nilpotent", "torsion-free",
                  "periodic", "residually-finite", "linear", "free", "free-abelian", "p-group",
                  "exponent-2", "exponent-3", "bounded-exponent", "polycyclic", "odd-order", "two-primes",
                  "countable", "left-orderable", "bi-orderable", "amenable", "residually-nilpotent",
                  "metabelian", "class-2", "dedekind")

    def _embeds_axioms(self):
        """Вложение A ↪ B: только для атомов, которые уже есть (иначе пар — квадрат
        числа термов). Наследование свойств подгрупп, ≅ ⇒ ↪, подгруппа и множители
        вкладываются, взаимное вложение конечных — ≅, тривиальная вкладывается всюду."""
        emb = [a for a in self.atoms if a[0] == "r" and a[1] == "embeds"]
        props = {}
        for a in self.atoms:
            if a[0] == "p":
                props.setdefault(a[2], set()).add(a[1])
        for atom in emb:
            _, _, a, b = atom
            e = self.var[atom]
            why = "вложение"
            for p in self.SUB_CLOSED:
                if p in props.get(b, ()) and self.v.prop_fits(p, self.g.terms[a].sort):
                    self._add([-e, -self.lit(("p", p, b)), self.lit(("p", p, a))], f"{why}: наследует {p}")
            iso = self.lit(("r", "iso", a, b)) if ("r", "iso", *sorted((a, b), key=str)) in self.var else None
            if iso is not None and iso is not False:
                self._add([-iso, e], f"{why}: ≅ ⇒ ↪")
                if ("r", "embeds", b, a) in self.var:
                    self._add([-e, -self.lit(("r", "embeds", b, a)), -self.lit(("p", "finite", a)), iso],
                              f"{why}: взаимное вложение конечных ⇒ ≅")
            self._add([-self.lit(("p", "trivial", a)), e], f"{why}: тривиальная вкладывается")
            # Хигман (⇒): к. п. подгруппа к. о. группы рекурсивно определена
            if {"fin-pres"} <= props.get(b, set()) and {"fin-gen", "rec-pres"} <= props.get(a, set()):
                self._add([-e, -self.lit(("p", "fin-pres", b)), -self.lit(("p", "fin-gen", a)),
                           self.lit(("p", "rec-pres", a))], f"{why}: Хигман, к. п. подгруппа к. о. — р. о.")
            info = self.g.terms[a]
            if info.links.get("ambient") == b:
                self._add([e], f"{why}: подгруппа")
            if isinstance(b, App) and b.op in ("prod", "freeprod", "wreath") and a in b.args:
                self._add([e], f"{why}: множитель {b.op}")

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
            # тривиальные группы изоморфны — только для уже заведённых пар
            # (правилом на все пары: квадрат атомов, и транзитивность ≅ отключается)
            if rel == "iso" and "trivial" in obj_props and all(
                    self.v.prop_fits("trivial", self.g.terms[x].sort) for x in (a, b)):
                self._add([-self.lit(("p", "trivial", a)), -self.lit(("p", "trivial", b)), e],
                          "iso: тривиальные изоморфны")
            # подгруппы одной группы: обе — вся группа или обе тривиальны ⇒ равны
            if rel == "eq-sub":
                for p in ("whole", "trivial"):
                    if all(self.v.prop_fits(p, self.g.terms[x].sort) for x in (a, b)):
                        self._add([-self.lit(("p", p, a)), -self.lit(("p", p, b)), e], f"eq-sub: обе {p}")
            ps = props.get(a, set()) | props.get(b, set())
            for p in sorted(ps):  # порядок — для одной нумерации атомов на всех машинах
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
        # вложение: транзитивность по тройкам, где оба звена уже есть
        emb = {(a[2], a[3]) for a in self.atoms if a[0] == "r" and a[1] == "embeds"}
        succ = {}
        emb_order = sorted(emb, key=str)
        for a, b in emb_order:
            succ.setdefault(a, []).append(b)
        for a, b in emb_order:
            for c in succ.get(b, []):
                if c != a and (a, c) in emb:
                    self._add([-self.lit(("r", "embeds", a, b)), -self.lit(("r", "embeds", b, c)),
                               self.lit(("r", "embeds", a, c))], "embeds: транзитивность")
        groups = []
        for rel, ps in by_rel.items():
            nodes = sorted({x for p in ps for x in p}, key=str)
            if rel == "eq-sub":  # равенство — только у подгрупп одной группы
                amb = {}
                for x in nodes:
                    amb.setdefault(self.g.terms[x].links.get("ambient"), []).append(x)
                groups += [(rel, ns) for ns in amb.values()]
            else:
                groups.append((rel, nodes))
        for rel, nodes in groups:
            if len(nodes) > 40:
                # много термов: все тройки — куб клауз; берём треугольники из уже
                # заведённых пар (раньше транзитивность здесь выключалась целиком)
                key = lambda x, y: ("r", rel, *sorted((x, y), key=str))
                adj = {}
                for x in nodes:
                    for y in nodes:
                        if x != y and key(x, y) in self.var:
                            adj.setdefault(x, set()).add(y)
                order = {x: i for i, x in enumerate(sorted(nodes, key=str))}
                for a in adj:
                    for b in sorted(adj[a], key=str):
                        if order[b] <= order[a]:
                            continue
                        for c in sorted(adj[a] & adj.get(b, set()), key=str):
                            if order[c] <= order[b]:
                                continue
                            ab, bc, ac = self.lit(key(a, b)), self.lit(key(b, c)), self.lit(key(a, c))
                            self._add([-ab, -bc, ac], f"{rel}: транзитивность (треугольники)")
                            self._add([-ab, -ac, bc], f"{rel}: транзитивность (треугольники)")
                            self._add([-bc, -ac, ab], f"{rel}: транзитивность (треугольники)")
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
