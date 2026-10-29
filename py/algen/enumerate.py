"""Перебор условий на форме схемы и отсев (этап 4).

Форма — вершины и конструкции без свойств, здесь «G, N ⩽ G, G/N». Условие —
набор посылок (литералов над атомами формы) и цель-литерал. Перебор идёт по
числу посылок, отсев — в таком порядке:

1. **Контрпример из библиотеки.** Каждая пара (G, N) библиотеки даёт строку
   истинности по всем атомам (записанные значения и выведенные из них).
   Условие опровергнуто, если есть строка, где посылки верны, а цель ложна.
   Это булевы операции над столбцами матрицы, без решателя.
2. **Минимальность.** Если без какой-то посылки условие тоже не опровергнуто,
   оно ослабляется: остаётся только слабейшая версия.
3. **Вывод.** Для выживших SAT-решатель проверяет, следует ли цель из
   посылок по базе правил, и не противоречивы ли посылки.

Остаток — то, что не закрыли ни библиотека, ни база. Каждая строка остатка —
либо недостающий пример, либо недостающее правило, либо факт для архива.
Условие и его контрапозиции — один и тот же запрет «не бывает одновременно
A, B, C», поэтому остаток печатается запретами. Если у какой-то пары
библиотеки посылки верны, а значение цели не записано, отчёт подсказывает,
какое значение заполнить.

Контрпример закрывает условие, только если не держится на помеченных
значениях. Если он держится на значении с пометкой «трудно» (теореме),
условие идёт в «трудный контрпример»: это кандидат в архив. Если на
«коротком доводе» (несколько строк, но не учебный факт) — в корзину
«короткий довод», которая в выдаче скрыта (показать: --короткие).
Условия, посылкам которых не удовлетворяет ни одна пара библиотеки, идут
отдельно: это вопросы существования.

    cd py && python3 -m algen.enumerate --посылок 2
"""

import argparse
import json
import sys
from collections import Counter, defaultdict
from itertools import combinations, permutations

import numpy as np

from types import SimpleNamespace

from .library import GROUP_PROPS, MARKS, SUB_PROPS, Library, Scene, Search, built_library, jobs
from .logic import App, Theory, Var, Vocab, decide

# Свойства, которые не входят в атомы формы (флаг --без): схемы с большим
# числом термов растут комбинаторно с каждым свойством.
SKIP = set()
MOR_PROPS = ("injective", "surjective", "iso", "zero-mor")
RELATIONS = True  # атомы-отношения между термами схемы (⩽, =, ≅)
DIVERSE = 4  # моделей «наоборот» в _derive


def relation_atoms(g, terms):
    """⩽ и = для подгрупп одной группы, ≅ для групп (в том числе подгрупп как
    групп). Симметричные — с аргументами по возрастанию строки, как в Theory.lit."""
    out = []
    subs = [t for t in terms if g.terms[t].sort == "Grp.sub"]
    objs = [t for t in terms if g.v.fits(g.terms[t].sort, "Grp.obj")]
    for i, a in enumerate(subs):
        for b in subs:
            if a != b and g.terms[a].links.get("ambient") == g.terms[b].links.get("ambient"):
                out.append(("r", "le", a, b))
                if str(a) < str(b):
                    out.append(("r", "eq-sub", a, b))
    for i, a in enumerate(objs):
        for b in objs[i + 1:]:
            x, y = sorted((a, b), key=str)
            out.append(("r", "iso", x, y))
    return out


def props():
    return [p for p in GROUP_PROPS if p not in SKIP]


def atom_name(a):
    return f"{a[1]}({', '.join(map(str, a[2:]))})"


def lit_name(a, v):
    return ("" if v else "¬") + atom_name(a)


# --- подсхемы и симметрии ---------------------------------------------------------

COMMUTATIVE = {"prod", "freeprod"}


def term_vars(t):
    if isinstance(t, Var):
        return {t}
    return set().union(*(term_vars(a) for a in t.args))


def atom_vars(a, graph):
    """Переменные, о которых говорит атом. Свойство вложения (normal(N))
    говорит и об объемлющей группе, свойство N как группы — только об N.
    Отношение — о всех своих аргументах."""
    if a[0] == "r":
        return set().union(*(term_vars(x) for x in a[2:]))
    out = term_vars(a[2])
    if a[1] in SUB_PROPS:
        amb = graph.terms[a[2]].links.get("ambient")
        if amb is not None:
            out |= term_vars(amb)
    return out


def canon(t, perm):
    if isinstance(t, Var):
        return perm.get(t, t).name
    args = [canon(x, perm) for x in t.args]
    if t.op in COMMUTATIVE:
        args.sort()
    return f"{t.op}({', '.join(args)})"


def canon_atom(a, perm):
    """Строка атома с переименованными переменными; у симметричных отношений
    аргументы упорядочены."""
    args = [canon(x, perm) for x in a[2:]]
    if a[0] == "r" and a[1] in ("iso", "eq-sub"):
        args.sort()
    return f"{a[1]}({', '.join(args)})"


def symmetries(graph, atoms, fixed):
    """Перестановки переменных, которые сохраняют сорта, связи, набор атомов
    формы и посылки схемы. Условия, переходящие друг в друга, — одно условие."""
    vs = [t for t in graph.terms if isinstance(t, Var)]
    base = {canon_atom(a, {}) for a in atoms}
    fixed_c = {(canon_atom(a, {}), v) for a, v in fixed}
    out = []
    for p in permutations(vs):
        perm = dict(zip(vs, p))
        if any(graph.terms[v].sort != graph.terms[perm[v]].sort
               or {k: perm.get(x, x) for k, x in graph.terms[v].links.items()} != graph.terms[perm[v]].links
               for v in vs):
            continue
        if {canon_atom(a, perm) for a in atoms} != base:
            continue
        if {(canon_atom(a, perm), v) for a, v in fixed} != fixed_c:
            continue
        out.append(perm)
    return out


def klass(lits, perms):
    """Канонический запрет: множество литералов с точностью до симметрий."""
    return min(tuple(sorted(("" if v else "¬") + canon_atom(a, perm) for a, v in lits))
               for perm in perms)


class Form:
    """Форма «G, N, G/N»: атомы, матрица значений по библиотеке, теория."""

    def __init__(self, lib, vocab):
        self.sc, self.lib, self._kept = Scene(vocab), lib, {}
        sc = self.sc
        self.atoms = ([("p", p, sc.G) for p in props()]
                      + [("p", p, sc.N) for p in SUB_PROPS]
                      + [("p", p, sc.N) for p in props()]
                      + [("p", p, sc.Q) for p in props()])
        self.index = {a: i for i, a in enumerate(self.atoms)}
        normal = 2 * self.index[("p", "normal", sc.N)]
        # Атом i имеет смысл, только если посылки содержат столбцы req[i]:
        # G/N существует при нормальной N.
        self.req = {i: {normal} for i, a in enumerate(self.atoms) if a[2] == sc.Q}
        self.fixed = []  # столбцы, верные во всех условиях формы
        # Три матрицы: m — все значения, s — без «трудно», e — ещё и без
        # «короткого довода», то есть только понятные.
        levels = {"m": (), "s": ("трудно",), "e": MARKS}
        rows, names = {k: [] for k in levels}, []
        for key, sub in jobs(lib, lib.obj):
            if sub is None:
                continue
            o = lib.obj[key]
            full = None
            for k, drop in levels.items():
                if full is not None and not (drop and sc.hard_atoms(lib, key, sub, drop)):
                    rows[k].append(full)
                    continue
                vals = (sc.values(lib, key, sub, self.atoms, drop=drop) if not o["конечная"]
                        else {a: v for a, (v, _) in sc.facts(lib, key, sub).items()})
                rows[k].append([vals.get(a) for a in self.atoms])
                full = full or rows[k][-1]
            names.append((key, sub))
        # Столбец 2i — «атом i верен», 2i + 1 — «атом i ложен».
        self.m, self.s, self.e = (self._matrix(rows[k]) for k in levels)
        self.names = names

    def _matrix(self, rows):
        m = np.zeros((len(rows), 2 * len(self.atoms)), dtype=bool)
        for r, row in enumerate(rows):
            for i, v in enumerate(row):
                if v is not None:
                    m[r, 2 * i + (0 if v else 1)] = True
        return m

    def unknown_goal(self, prem, g):
        """Строка, где посылки верны, а значение цели не записано и не
        выводится: заполнив его, можно закрыть условие. Записанные группы
        предпочтительнее построенных произведений."""
        rows = np.flatnonzero(self.m[:, list(prem) + self.fixed].all(axis=1) & ~self.m[:, g] & ~self.m[:, g ^ 1])
        if not len(rows):
            return None
        return min(rows, key=self.synthetic)

    def unknown_rows(self, prem, g):
        """Все строки, где посылки верны, а значение цели не записано и не выводится."""
        return np.flatnonzero(self.m[:, list(prem) + self.fixed].all(axis=1) & ~self.m[:, g] & ~self.m[:, g ^ 1])

    def _image(self, r, t):
        """Образ терма t в строке r: ("obj", ключ) или ("sub", ключ, номер)."""
        key, sub = self.names[r]
        if t == self.sc.G:
            return ("obj", key)
        if t == self.sc.N:
            return ("sub", key, sub)
        q = self.lib.obj[key]["подгруппы"][sub].get("фактор")
        return ("obj", q) if q else None

    def one_unknown(self, cols):
        """Строки, где ни один литерал запрета (столбцы cols) не ложен, а
        неизвестен ровно один: заполнив его, можно закрыть запрет.
        Возвращает [(строка, столбец неизвестного литерала)]."""
        cols = list(cols) + self.fixed
        tr, fa = self.m[:, cols], self.m[:, [c ^ 1 for c in cols]]
        unk = ~tr & ~fa
        rows = np.flatnonzero(~fa.any(axis=1) & (unk.sum(axis=1) == 1))
        return [(r, cols[int(np.flatnonzero(unk[r])[0])]) for r in rows]

    def value_name(self, r, atom):
        """Имя недостающего значения атома в строке r — «решающее значение».
        Значение у построенного произведения приписывается множителю, у которого
        не записано больше значений: обычно оно оттуда и берётся."""
        if atom[0] == "r":
            # отношение: приписываем группе (множителю произведения), где оно не записано
            vs = sorted(set().union(*(term_vars(x) for x in atom[2:])), key=str)
            keys = [self._image(r, v) for v in vs]
            keys = [base_factor(self.lib, k[1], None) for k in keys if k and k[0] == "obj"]
            where = ", ".join(self.lib.obj[k].get("имя", k) for k in keys) or self.where(r)
            return f"{atom_name(atom)} у {where}"
        im = self._image(r, atom[2])
        t = atom[2]
        if im is not None and im[0] == "mor":
            return f"{atom_name(atom)} у {self.where(r)}"
        if im is None and isinstance(t, App) and t.op in ("center", "commutator", "quotient"):
            # Не записан центр или коммутант: приписываем это группе, у которой его нет.
            g = t.args[0]
            gim = self._image(r, g)
            if gim is not None and gim[0] == "obj":
                field = "коммутант" if t.op == "commutator" else "центр"
                key = base_factor(self.lib, gim[1], None, field)
                return f"не записан {field} у {self.lib.obj[key].get('имя', key)}"
        if im is None:
            return f"{atom_name(atom)} у {self.where(r)}"
        p, lib = atom[1], self.lib
        if im[0] == "sub" and p in SUB_PROPS:
            key, what = im[1], f"{p}({atom[2]})"
        else:
            key = im[1] if im[0] == "obj" else lib.obj[im[1]]["подгруппы"][im[2]]["≅"]
            what = p
            key = base_factor(lib, key, p)
            return f"{what}({lib.obj[key].get('имя', key)})"
        key = base_factor(lib, key, None)
        return f"{what} у {lib.obj[key].get('имя', key)}"

    def refuters(self, prem, g, m=None):
        """Строки матрицы (по умолчанию m), где посылки верны, а цель ложна."""
        m = self.m if m is None else m
        neg = g + 1 if g % 2 == 0 else g - 1
        return np.flatnonzero(m[:, list(prem) + self.fixed + [neg]].all(axis=1))

    def lit(self, j):
        """Номер столбца → (атом, значение)."""
        return self.atoms[j // 2], j % 2 == 0

    def synthetic(self, r):
        """Строка из построенного произведения: такие показываем последними."""
        return "×" in self.names[r][0]

    def where(self, r):
        key, sub = self.names[r]
        return f"G = {key}, N = {self.lib.obj[key]['подгруппы'][sub]['id']}"

    def marked(self, r, mark):
        """Помеченные mark атомы строки r: [(атом, имя факта)]."""
        key, sub = self.names[r]
        return [(a, self.sc.marked_name(self.lib, key, sub, a, mark))
                for a in sorted(self.sc.hard_atoms(self.lib, key, sub, (mark,)), key=str)]

    def row_keeping(self, r, keep, mark):
        """Строка пары r, где из значений с пометкой mark оставлены только
        атомы keep. При mark = «трудно» короткий довод разрешён, как в s."""
        k = (r, keep, mark)
        if k not in self._kept:
            key, sub = self.names[r]
            drop = ("трудно",) if mark == "трудно" else MARKS
            hard = self.sc.hard_atoms(self.lib, key, sub, drop) - keep
            facts = {a: x for a, x in self.sc.facts(self.lib, key, sub).items() if a not in hard}
            vals = {a: v for a, (v, _) in facts.items()}
            vals.update(self.sc.derive(facts, [a for a in self.atoms if a not in vals]))
            self._kept[k] = self._matrix([[vals.get(a) for a in self.atoms]])[0]
        return self._kept[k]

    def deciding(self, prem, g, mark, limit=40):
        """На каких помеченных mark значениях держится опровержение условия.
        Для каждой из первых limit строк-опровержений (записанные группы
        раньше произведений) — наименьшие наборы помеченных значений, которых
        хватает. Возвращает {набор имён вида «hopfian(BS23)»: строка}."""
        mat = self.s if mark == "короткий довод" else self.m
        cols = list(prem) + self.fixed + [g ^ 1]
        rows = sorted(self.refuters(prem, g, mat), key=self.synthetic)[:limit]
        out = {}
        for r in rows:
            named = dict(self.marked(r, mark))
            marked = sorted(named, key=str)
            hit = []
            for size in range(1, min(len(marked), 3) + 1):
                hit = [k for k in combinations(marked, size)
                       if self.row_keeping(r, frozenset(k), mark)[cols].all()]
                if hit:
                    break
            for k in hit or [marked]:
                out.setdefault(frozenset(named[a] for a in k), r)
        return out


class SchemeForm(Form):
    """Форма по схеме: «∀ A : Grp; ∀ B : Grp» и термы вроде «A × B».

    Строки — подстановки библиотеки в переменные схемы (как в Search),
    столбцы — свойства переменных и названных термов. Посылки из записи
    схемы («∀ H : Sub(G) | abelian(H)») входят во все условия."""

    def __init__(self, lib, vocab, decl, terms=(), max_subs=None, grow_ops=None, part=None, with_rows=True):
        """part = (i, n): считать только строки с номерами i - 1, i - 1 + n, …;
        with_rows=False — без строк (каркас для таблицы базы)."""
        from .etalon import scheme, term
        g, fixed, _ = scheme(vocab, {"раздел": "grp", "условие": decl})
        names = {str(t): t for t in g.terms}
        own = list(g.terms)
        for x in terms:
            t = term(g, x, names, "grp")
            if t not in own:
                own.append(t)
        self.g, self.lib, self._kept = g, lib, {}
        T = Theory(g, grow=1, extra=relation_atoms(g, own) if RELATIONS else (), grow_ops=grow_ops)
        self.sc = SimpleNamespace(T=T, s=T.solver())
        self.search = Search(g, T, lib)
        self.atoms = []
        for t in own:
            sort = g.terms[t].sort
            if sort == "Grp.obj":
                self.atoms += [("p", p, t) for p in props()]
            elif sort == "Grp.sub":
                self.atoms += [("p", p, t) for p in list(SUB_PROPS) + props()]
            elif sort == "Grp.mor":
                self.atoms += [("p", p, t) for p in MOR_PROPS]
        if RELATIONS:
            self.atoms += relation_atoms(g, own)
        self.index = {a: i for i, a in enumerate(self.atoms)}
        self.req = {}
        for i, a in enumerate(self.atoms):
            need = {2 * self.index[("p", p, u)] for p, u in g.requires(a[2]) if ("p", p, u) in self.index}
            if need:
                self.req[i] = need
        self.fixed = [2 * self.index[a] + (0 if v else 1) for a, v in fixed if a in self.index]
        self.fixed_lits = fixed
        levels = {"m": (), "s": ("трудно",), "e": MARKS}
        rows, self.envs, self.skipped = {k: [] for k in levels}, [], []
        self._facts = {}  # записанные значения строк — лениво, только для разбора помеченных
        derived = self._derived = {}  # кэш вывода: одинаковые наборы записанных значений — одна строка
        self.own = own
        if not with_rows:
            return
        for n_env, env in enumerate(self.search._assign(0, {})):
            if part and n_env % part[1] != part[0] - 1:
                continue
            if max_subs and any(im[0] == "sub" and im[2] >= max_subs for im in env.values()):
                continue
            facts, hard = self.search.facts(env)
            assume = [l for a, v in facts.items() if (l := T.lit(a, v)) not in (None, False)]
            if not self.sc.s.solve(assumptions=assume):
                self.skipped.append(self.where_env(env))  # записи противоречат базе
                continue
            full = None
            for k, drop in levels.items():
                if full is not None and not any(m in drop for m, _ in hard.values()):
                    rows[k].append(full)
                    continue
                f = {a: v for a, v in facts.items() if not (a in hard and hard[a][0] in drop)}
                key = self._key(f)
                row = derived.get(key)
                if row is None:
                    row = derived[key] = self._derive(f)
                rows[k].append(row)
                full = full or row
            self.envs.append(dict(env))
        self.m, self.s, self.e = (self._matrix(rows[k]) for k in levels)
        self.names = list(range(len(self.envs)))

    def _key(self, f):
        """Компактный ключ набора значений для кэша вывода."""
        T = self.sc.T
        return np.array(sorted(l for a, v in f.items() if type(l := T.lit(a, v)) is int),
                        dtype=np.int32).tobytes()

    def row_facts(self, r):
        if r not in self._facts:
            self._facts[r] = self.search.facts(self.envs[r])
        return self._facts[r]

    def _derive(self, facts):
        """Значения атомов, следующие из записанных: ядро («backbone») решателя.
        Одна модель задаёт кандидата для каждого атома; атом проверяется одним
        вызовом, а атомы, которые разошлись с найденными моделями, — неизвестны."""
        T, s = self.sc.T, self.sc.s
        assume = [l for a, v in facts.items() if (l := T.lit(a, v)) not in (None, False)]
        lits = {a: T.lit(a) for a in self.atoms if a not in facts}
        lits = {a: l for a, l in lits.items() if type(l) is int}  # 1 == True в Python: сравнивать нельзя
        if not s.solve(assumptions=assume):
            return [facts.get(a) for a in self.atoms]
        model = set(s.get_model())
        # Единичное распространение даёт большую часть следствий почти даром.
        ok, implied = s.propagate(assumptions=assume)
        implied = set(implied or ())
        val = {}
        for a, l in list(lits.items()):
            if l in implied:
                val[a] = True
                del lits[a]
            elif -l in implied:
                val[a] = False
                del lits[a]
        seen_t = {a for a, l in lits.items() if l in model}      # встречалось «верно»
        seen_f = {a for a, l in lits.items() if -l in model}     # встречалось «ложно»
        # Модели «наоборот»: решателю предлагаем противоположные значения всех
        # атомов, у которых пока одно значение, — одна модель снимает сразу многие.
        for _ in range(DIVERSE):
            one = [(a, l) for a, l in lits.items() if (a in seen_t) != (a in seen_f)]
            if not one:
                break
            s.set_phases([-l if a in seen_t else l for a, l in one])
            if not s.solve(assumptions=assume):
                break
            m = set(s.get_model())
            new = 0
            for a, l in one:
                if a in seen_t and -l in m:
                    seen_f.add(a)
                    new += 1
                elif a in seen_f and l in m:
                    seen_t.add(a)
                    new += 1
            if new == 0:
                break
        for a, l in lits.items():
            if a in seen_t and a in seen_f:
                continue
            if a not in seen_t and a not in seen_f:
                # переменной нет в модели (решатель её не видел): две проверки
                if not s.solve(assumptions=assume + [-l]):
                    val[a] = True
                elif not s.solve(assumptions=assume + [l]):
                    val[a] = False
                continue
            want = a in seen_t  # единственное пока значение
            if s.solve(assumptions=assume + [-l if want else l]):
                m = set(s.get_model())
                for b, lb in lits.items():
                    if lb in m:
                        seen_t.add(b)
                    elif -lb in m:
                        seen_f.add(b)
            else:
                val[a] = want
        return [facts[a] if a in facts else val.get(a) for a in self.atoms]

    def synthetic(self, r):
        return any(im[0] == "obj" and self.lib.obj[im[1]].get("синтез") for im in self.envs[r].values())

    def _image(self, r, t):
        return self.search._image(t, self.envs[r])

    def where(self, r):
        return self.where_env(self.envs[r])

    def where_env(self, env):
        return ", ".join(f"{t} = {self.search._name(im)}" for t, im in env.items())

    def marked(self, r, mark):
        _, hard = self.row_facts(r)
        return sorted(((a, name) for a, (m, name) in hard.items() if m == mark), key=lambda x: str(x[0]))

    def row_keeping(self, r, keep, mark):
        k = (r, keep, mark)
        if k not in self._kept:
            facts, hard = self.row_facts(r)
            drop = ("трудно",) if mark == "трудно" else MARKS
            f = {a: v for a, v in facts.items() if not (a in hard and hard[a][0] in drop and a not in keep)}
            key = self._key(f)
            row = self._derived.get(key)
            if row is None:
                row = self._derived[key] = self._derive(f)
            self._kept[k] = self._matrix([row])[0]
        return self._kept[k]


def _unknowns(o):
    """Сколько у записи не хватает: незаписанные свойства, центр, коммутант."""
    return (sum(o["свойства"].get(p) is None for p in GROUP_PROPS)
            + (o.get("центр") is None) + (o.get("коммутант") is None))


def base_factor(lib, key, p, field=None):
    """Для построенного произведения A × B — множитель, к которому относится
    недостающее значение свойства p (None — для подгрупп) или незаписанное
    поле field («центр», «коммутант»): тот, у которого его нет, а если неясно —
    у которого вообще меньше записано. Для записанных групп — сама группа."""
    o = lib.obj.get(key)
    if not o or not o.get("синтез"):
        return key
    inv = getattr(lib, "_prod_inv", None)
    if inv is None:
        inv = lib._prod_inv = {k: ab for ab, k in lib.prod.items()}
    a, b = inv.get(key, (None, None))
    if a is None:
        return key
    fa, fb = (base_factor(lib, x, p, field) for x in (a, b))
    oa, ob = lib.obj[fa], lib.obj[fb]
    if field is not None:
        ua, ub = oa.get(field) is None, ob.get(field) is None
        if ua != ub:
            return fa if ua else fb
    if p is not None:
        ua, ub = oa["свойства"].get(p) is None, ob["свойства"].get(p) is None
        if ua != ub:
            return fa if ua else fb
    ua, ub = _unknowns(oa), _unknowns(ob)
    if ua == ub:
        return key
    return fa if ua > ub else fb


def decisive(classes_opts):
    """Жадное покрытие: {запрет: множество имён значений} → [(имя, [запреты])].
    Каждый запрет попадает к первому выбранному значению, которое его касается."""
    left = {t for t, o in classes_opts.items() if o}
    out = []
    while left:
        cnt = Counter(v for t in left for v in classes_opts[t])
        best = max(cnt, key=lambda v: (cnt[v], v))
        hit = sorted(t for t in left if best in classes_opts[t])
        out.append((best, hit))
        left -= set(hit)
    return out


def cover(options):
    """Жадно выбрать факты, чтобы у каждого условия один из его наборов
    (options[i] — список frozenset) был выбран целиком. Возвращает для
    каждого условия выбранный набор: решающий факт условия."""
    chosen, left, out = set(), set(range(len(options))), [None] * len(options)
    inv = defaultdict(set)  # элемент набора → условия, где он встречается
    for i, opts in enumerate(options):
        for t in opts:
            for e in t:
                inv[e].add(i)
    while left:
        def gain(c):
            new = c - chosen
            if not new:
                return 0
            cand = set().union(*(inv[e] for e in new)) & left
            n = sum(1 for i in cand if any(t <= chosen | c for t in options[i]))
            return n / len(new)
        best = max({c for i in left for c in options[i]}, key=lambda c: (gain(c), sorted(c)))
        chosen |= best
        for i in list(left):
            fit = [t for t in options[i] if t <= chosen]
            if fit:
                out[i] = min(fit, key=lambda t: (len(t), sorted(t)))
                left.discard(i)
    return out


def enumerate_form(form, max_prem, goals=None, m=None):
    """Все минимальные условия не длиннее max_prem посылок, которые библиотека
    не опровергает (по матрице m, по умолчанию — только понятными значениями).
    Неминимальные (с неопровергнутым подусловием) не хранятся: при слабой
    библиотеке их миллионы. Возвращает (неопровергнутые минимальные, без
    примера); общее число неопровергнутых — в form.n_alive."""
    m = form.e if m is None else m
    n_lit = m.shape[1]
    goal_cols = range(n_lit) if goals is None else goals
    alive, empty, lower = {}, [], set()
    count = 0
    # Покрытие (схемы из таблицы базы): условие должно касаться каждого
    # «верхнего» элемента схемы, иначе оно — факт меньшей схемы и выдаётся там.
    need = getattr(form, "need", None)
    if need:
        amask = np.zeros(n_lit // 2, dtype=np.int64)
        for b, grp in enumerate(need):
            for i in grp:
                amask[i] |= 1 << b
        lmask = np.repeat(amask, 2)
        full = (1 << len(need)) - 1
    every = np.arange(m.shape[0])

    def proper_subsets(prem):
        for r in range(1, len(prem)):
            yield from combinations(prem, r)

    def alive_direct(q, g):
        """Подусловие (q, g) не опровергнуто (для минимальности при покрытии)."""
        have = set(q) | set(form.fixed)
        if not all(form.req.get(j // 2, set()) <= have for j in list(q) + [g]):
            return False
        rows = every
        for j in q:
            rows = rows[m[rows, j]]
        return rows.size > 0 and not m[rows, g ^ 1].any()

    def go(prem, rows, start, depth, pm=0):
        nonlocal count
        if need:
            miss = full & ~pm
            if bin(miss).count("1") > 2 * (depth - len(prem) + 1):
                return  # не хватит литералов, чтобы коснуться всех элементов
        if len(prem) == depth:
            atoms = {j // 2 for j in prem}
            have = set(prem) | set(form.fixed)
            if not all(form.req.get(i, set()) <= have for i in atoms):
                return
            if rows.size == 0:
                empty.append(tuple(prem))
                return
            sub = m[rows]
            gc = goal_cols
            if need:
                miss = full & ~pm
                ok = (lmask & miss) == miss
                gc = [g for g in goal_cols if ok[g]]
                if not gc:
                    return
            negs = sub[:, [g ^ 1 for g in range(n_lit)]].any(axis=0) if len(gc) > 40 else None
            for g in gc:
                if g // 2 in atoms or not form.req.get(g // 2, set()) <= have:
                    continue
                if (negs[g] if negs is not None else sub[:, g ^ 1].any()):
                    continue
                count += 1
                key = (tuple(prem), g)
                if depth < max_prem:
                    lower.add(key)
                if need:
                    if any(alive_direct(q, g) for q in proper_subsets(prem)):
                        continue
                elif any((q, g) in lower for q in proper_subsets(prem)):
                    continue
                alive[key] = int(sub[:, g].sum())
            return
        for j in range(start, n_lit):
            if j // 2 in {x // 2 for x in prem}:
                continue
            nxt = rows[m[rows, j]] if prem else np.flatnonzero(m[:, j])
            go(prem + [j], nxt, j + 1, depth, pm | (int(lmask[j]) if need else 0))

    start = np.flatnonzero(m[:, form.fixed].all(axis=1)) if form.fixed else np.arange(m.shape[0])
    for depth in range(1, max_prem + 1):
        go([], start, 0, depth)
    form.n_alive = count
    return alive, empty


def minimal(alive):
    """Оставить условия, у которых без любой посылки цель опровергается."""
    out = {}
    for (prem, g), support in alive.items():
        if all((tuple(x for x in prem if x != p), g) not in alive for p in prem if len(prem) > 1):
            out[prem, g] = support
    return out


def run(max_prem, lib=None, vocab=None, form=None):
    vocab = vocab or Vocab.section("grp")
    if lib is None:
        lib = built_library(vocab)
    form = form or Form(lib, vocab)
    fixed = getattr(form, "fixed_lits", [])
    graph = form.sc.T.g
    allvars = {t for t in graph.terms if isinstance(t, Var)}
    perms = symmetries(graph, form.atoms, fixed)
    degen = []
    for t in sorted(allvars, key=str):
        sort = graph.terms[t].sort
        if sort == "Grp.obj" and len(allvars) > 1:
            degen.append((("p", "trivial", t), True))
        elif sort == "Grp.sub":
            degen += [(("p", "trivial", t), True), (("p", "whole", t), True)]
    alive, empty = enumerate_form(form, max_prem)
    mins = minimal(alive)
    report = []
    for (prem, g), support in mins.items():
        prem_l = [form.lit(j) for j in prem]
        goal = form.lit(g)
        # Условие только о части переменных — факт меньшей схемы.
        if set().union(*(atom_vars(a, graph) for a, _ in prem_l + [goal] + fixed)) != allvars:
            continue
        # Вырожденное: посылки заставляют группу быть тривиальной или
        # подгруппу — тривиальной или всей. Это тоже факт меньшей схемы.
        # Смотрим на весь запрет, чтобы контрапозиции решались одинаково.
        whole = fixed + prem_l + [(goal[0], not goal[1])]
        if any(decide(form.sc.T, whole, d, form.sc.s).kind == "выводится" for d in degen):
            continue
        v = decide(form.sc.T, fixed + prem_l, goal, form.sc.s)
        r = {"посылки": [lit_name(*x) for x in prem_l], "цель": lit_name(*goal),
             "запрет": sorted([lit_name(*x) for x in prem_l] + [lit_name(goal[0], not goal[1])]),
             "класс": klass(prem_l + [(goal[0], not goal[1])], perms),
             "примеров": support, "вердикт": v.kind,
             "ядро": [lit_name(*x) for x in v.core or []]}
        if v.kind == "неизвестно":
            hint = form.unknown_goal(prem, g)
            if hint is not None:
                r["заполнить"] = {"где": form.where(hint), "атом": atom_name(goal[0])}
            # Решающие значения: строки, где неизвестен ровно один литерал запрета.
            r["значения"] = sorted({form.value_name(x, form.lit(c)[0])
                                    for x, c in form.one_unknown(list(prem) + [g ^ 1])})
        # Опровергается только помеченным значением: условие не закрыто.
        for mat, mark, kind in ((form.s, "короткий довод", "короткий довод"),
                                (form.m, "трудно", "трудный контрпример")):
            if not len(form.refuters(prem, g, mat)):
                continue
            r["вердикт"] = "ОШИБКА: выводится, а библиотека опровергает" if v.kind == "выводится" else kind
            r["_держится"] = (mark, form.deciding(prem, g, mark))
            break
        report.append(r)
    # Решающий факт: наименьший набор помеченных значений, общий для многих
    # условий. Тысяча условий так сводится к десятку фактов.
    for mark in MARKS:
        rs = [r for r in report if r.get("_держится", (None,))[0] == mark]
        for r, fact in zip(rs, cover([list(r["_держится"][1]) for r in rs])):
            r["решающий факт"] = sorted(fact)
            r["контрпример"] = {"где": form.where(r["_держится"][1][fact]), mark: sorted(fact)}
    for r in report:
        r.pop("_держится", None)
    return form, alive, empty, report


def clusters(triples):
    """Сгруппировать запреты по общей паре литералов: «A & B & C₁», «A & B & C₂»
    — один вопрос о парах (G, N) с A и B, обычно один недостающий пример.
    Жадно: пара, общая для наибольшего числа ещё не взятых запретов.
    Возвращает [(пара, [третьи литералы])]."""
    left, out = set(triples), []
    while left:
        by_pair = defaultdict(list)
        for t in left:
            for i in range(len(t)):
                pair = t[:i] + t[i + 1:]
                by_pair[pair].append(t[i])
        pair, thirds = max(by_pair.items(), key=lambda x: (len(x[1]), x[0]))
        out.append((pair, sorted(thirds)))
        left -= {tuple(sorted(pair + (x,))) for x in thirds}
    return sorted(out, key=lambda x: (-len(x[1]), x[0]))


REGISTRY = DATA_DIR = None


def load_registry():
    """Реестр разобранных вопросов: data/registry/grp.json. Значения, имя которых
    содержит шаблон вопроса, и запреты из списка в выдаче сворачиваются в одну
    строку со ссылкой на номер вопроса."""
    from .logic import DATA
    p = DATA / "registry" / "grp.json"
    if not p.exists():
        return {"вопросы": [], "запреты": {}}
    with open(p, encoding="utf-8") as f:
        d = json.load(f)
    return {"вопросы": d.get("вопросы", []), "запреты": d.get("запреты", {})}


def registry_match(registry, value):
    for q in registry.get("вопросы", []):
        if any(p in value for p in q.get("шаблоны", [])):
            return q["№"]
    return None


def render(form, alive, empty, report, short=False, full=False, json_path=None,
           out=sys.stdout, err=sys.stderr, registry=None):
    """Печать отчёта о прогоне и сводка для пакетного режима (возвращается)."""
    registry = registry if registry is not None else load_registry()
    import builtins

    def print(*args, file=None, **kw):  # noqa: A001 — в out, а «file=sys.stderr» — в err
        builtins.print(*args, file=err if file is sys.stderr else out, **kw)

    # Считаем запреты: условие, его контрапозиции и симметричные ему — один.
    classes = {}
    for r in report:
        classes.setdefault(r["класс"], r)
    tally = Counter(r["вердикт"] for r in classes.values())
    print(f"строк в библиотеке {form.m.shape[0]}, литералов {form.m.shape[1]}", file=sys.stderr)
    print(f"не опровергнуто библиотекой {getattr(form, 'n_alive', len(alive))}, минимальных обо всех переменных {len(report)}, "
          f"запретов {len(classes)}: " + ", ".join(f"{k} {v}" for k, v in tally.most_common()), file=sys.stderr)
    print(f"посылок без единого примера: {len(empty)}", file=sys.stderr)
    for w in getattr(form, "skipped", [])[:5]:
        print(f"ПРОТИВОРЕЧИЕ в записях: {w}", file=sys.stderr)
    if json_path:
        with open(json_path, "w", encoding="utf-8") as f:
            json.dump({"остаток": [r for r in report if r["вердикт"] == "неизвестно"],
                       "трудный контрпример": [r for r in report if r["вердикт"] == "трудный контрпример"],
                       "короткий довод": [r for r in report if r["вердикт"] == "короткий довод"],
                       "выводится": sum(r["вердикт"] == "выводится" for r in report)},
                      f, ensure_ascii=False, indent=1)
    seen, hints, vals = {}, defaultdict(set), defaultdict(set)
    for r in report:
        if r["вердикт"] != "неизвестно":
            continue
        t = r["класс"]
        seen.setdefault(t, r["примеров"])
        vals[t] |= set(r.get("значения", ()))
        if r.get("заполнить"):
            h = r["заполнить"]
            hints[t].add(f"{h['атом']} у {h['где']}")
    # Сводка остатка по решающим значениям: одно незаписанное значение
    # (обычно у одной группы библиотеки) отвечает за десятки запретов.
    # Полный список запретов — ниже (--полностью) и в --json.
    dec = decisive({t: vals[t] for t in seen})
    bare = sorted(t for t in seen if not vals[t])
    # Реестр: разобранные значения и запреты сворачиваются в строку с номером.
    rz = registry.get("запреты", {})
    known = defaultdict(list)
    fresh = []
    for v, ts in dec:
        q = registry_match(registry, v)
        (known[q].extend(ts) if q else fresh.append((v, ts)))
    bare_fresh = []
    for t in bare:
        k = " & ".join(t)
        (known[rz[k]["№"]].append(t) if k in rz else bare_fresh.append(t))
    print(f"== решающих значений {len(fresh)}: касаются {sum(len(ts) for _, ts in fresh)} запретов; "
          f"без кандидата {len(bare_fresh)}; уже в реестре {sum(len(x) for x in known.values())} ==")
    for v, ts in fresh:
        print(f"значение {v} — запретов {len(ts)}; например: {' & '.join(ts[0])}")
    print(f"== без кандидата: нужен пример или правило ==")
    cl = clusters(bare_fresh)
    for pair, thirds in cl:
        if len(thirds) == 1:
            print(f"не бывает? {' & '.join(pair + tuple(thirds))}   [примеров посылок: {seen[tuple(sorted(pair + tuple(thirds)))]}]")
        else:
            print(f"не бывает? {' & '.join(pair)} & одно из: {', '.join(thirds)}   [запретов {len(thirds)}]")
    if known:
        print("== уже в реестре (data/registry/grp.json) ==")
        qs = {q["№"]: q for q in registry.get("вопросы", [])}
        for k, ts in sorted(known.items(), key=lambda x: -len(x[1])):
            print(f"{k} — запретов {len(ts)}: {qs.get(k, {}).get('вопрос', '')}")
    print(f"решающих значений {len(fresh)} на {sum(len(ts) for _, ts in fresh)} запретов, без кандидата {len(bare_fresh)} "
          f"в {len(cl)} кластерах, в реестре {sum(len(x) for x in known.values())}", file=sys.stderr)
    summary = {
        "запретов": len(classes), "вердикты": dict(tally), "остаток": len(seen),
        "значения": [{"имя": v, "запретов": len(ts), "пример": " & ".join(ts[0])} for v, ts in fresh],
        "без кандидата": [{"пара": list(pair), "третьи": thirds} for pair, thirds in cl],
        "реестр": {k: len(ts) for k, ts in known.items()},
    }
    groups = clusters(list(seen))
    if full:
        print("== все запреты остатка ==")
    for pair, thirds in groups if full else ():
        ts = [tuple(sorted(pair + (x,))) for x in thirds]
        hint = sorted(set().union(*(hints[t] for t in ts)))
        tail = "; заполнить " + ", ".join(hint[:3]) + (" …" if len(hint) > 3 else "") if hint else ""
        if len(thirds) == 1:
            print(f"не бывает? {' & '.join(ts[0])}   [примеров посылок: {seen[ts[0]]}{tail}]")
        else:
            print(f"не бывает? {' & '.join(pair)} & одно из: {', '.join(thirds)}   "
                  f"[запретов {len(thirds)}{tail}]")
    print(f"запретов без примера: {len(seen)}, кластеров: {len(groups)}", file=sys.stderr)
    for kind in ("трудный контрпример", "короткий довод"):
        groups = defaultdict(list)
        for r in classes.values():
            if r["вердикт"] == kind:
                groups[tuple(r["решающий факт"])].append(r)
        ranked = sorted(groups.items(), key=lambda x: (-len(x[1]), x[0]))
        summary[kind] = {" & ".join(f): len(rs) for f, rs in ranked}
        if kind == "короткий довод" and not short:
            if ranked:
                print(f"скрыто запретов с коротким доводом: {tally[kind]}, решающих фактов {len(ranked)}: "
                      + ", ".join(f"{' & '.join(f)} ({len(rs)})" for f, rs in ranked)
                      + " (показать: --короткие)", file=sys.stderr)
            continue
        for fact, rs in ranked:
            print(f"{kind}: {' & '.join(fact)} — запретов {len(rs)}")
            for r in rs:
                print(f"    бывает: {' & '.join(r['класс'])}   [{r['контрпример']['где']}]")
    return summary


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--посылок", dest="k", type=int, default=2)
    ap.add_argument("--схема", dest="decl", help="схема, например «∀ A : Grp; ∀ B : Grp»; по умолчанию форма G, N, G/N")
    ap.add_argument("--термы", dest="terms", default="", help="термы схемы через «;», например «A × B»")
    ap.add_argument("--подгрупп", dest="max_subs", type=int, default=None,
                    help="брать у каждой группы не больше стольких подгрупп")
    ap.add_argument("--json", dest="out", help="записать остаток и трудные контрпримеры в JSON")
    ap.add_argument("--короткие", dest="short", action="store_true",
                    help="показать и условия, опровергнутые только коротким доводом")
    ap.add_argument("--без", dest="skip", default="",
                    help="свойства через запятую, которые не перебирать, например bounded-exponent")
    ap.add_argument("--полностью", dest="full", action="store_true",
                    help="кроме сводки по решающим значениям, напечатать все запреты остатка кластерами")
    a = ap.parse_args()
    SKIP.update(x.strip() for x in a.skip.split(",") if x.strip())
    form = None
    if a.decl:
        vocab = Vocab.section("grp")
        lib = built_library(vocab)
        form = SchemeForm(lib, vocab, a.decl, [x for x in a.terms.split(";") if x.strip()], a.max_subs)
        form, alive, empty, report = run(a.k, lib, vocab, form)
    else:
        form, alive, empty, report = run(a.k)
    render(form, alive, empty, report, short=a.short, full=a.full, json_path=a.out)


if __name__ == "__main__":
    main()
