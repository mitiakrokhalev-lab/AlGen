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

import os
import numpy as np

from types import SimpleNamespace

from .library import GROUP_PROPS, MARKS, SUB_PROPS, Library, Scene, Search, built_library, jobs
from .logic import SYMMETRIC, App, Theory, Var, Verdict, Vocab, decide
from .conditions import PackedConditions, empty_like

# Свойства, которые не входят в атомы формы (флаг --без): схемы с большим
# числом термов растут комбинаторно с каждым свойством.
SKIP = set()
# Те же минимальные условия в числовых массивах. 0 — прежний словарь для сверки.
PACKED_CONDITIONS = os.environ.get("ALGEN_PACKED_CONDITIONS", "1") != "0"
MOR_PROPS = ("injective", "surjective", "iso", "zero-mor", "idempotent", "inner-aut")
ELT_PROPS = ("identity-elt", "involution", "central-elt", "real-elt", "commutator-elt", "generator")
GSET_PROPS = ("transitive", "faithful", "free-act", "regular", "primitive", "singleton-set", "finite-set")
RELATIONS = True  # атомы-отношения между термами схемы (⩽, =, ≅)
DIVERSE = 4  # моделей «наоборот» в _derive
# ALGEN_FAST=1: значения строки — записанные и единичное распространение, без
# поиска ядра решателем. На G даёт 91 % значений полного вывода в 15 раз
# быстрее; недостающие 9 % — меньше опровержений (больше вопросов), но не
# ошибки: каждое значение выведено. Для больших вселенных (размер ⩽ 2).
FAST_DERIVE = bool(os.environ.get("ALGEN_FAST"))
# Отсечение наборов посылок, не являющихся свободными (enumerate_form): выдача та же,
# меньше только счётчик «не опровергнуто библиотекой». ALGEN_PRUNE=0 — без отсечения.
PRUNE_FREE = os.environ.get("ALGEN_PRUNE", "1") != "0"
# Лист перебора векторами по целям (enumerate_form.leaf_vec); ALGEN_VEC=0 — прежний цикл.
VEC = os.environ.get("ALGEN_VEC", "1") != "0"
# Минимальность: маски целей как целые биты, выход после исключения всех целей.
# 0 — прежний полный обход для точной сверки результата и замеров.
EARLY_MIN = os.environ.get("ALGEN_EARLY_MIN", "1") != "0"
# Не обрабатывать битовые строки заранее недопустимых целей.
SPARSE_LEAF = os.environ.get("ALGEN_SPARSE_LEAF", "1") != "0"
NATIVE_ENUM = os.environ.get("ALGEN_NATIVE_ENUM", "1") != "0"
NATIVE_MINIMAL = os.environ.get("ALGEN_NATIVE_MINIMAL", "1") != "0"
# Перепись объёма выдачи: ALGEN_CENSUS=1 — run() останавливается после минимальности.
CENSUS = os.environ.get("ALGEN_CENSUS") == "1"
# Выборка состава (ALGEN_SAMPLE=N): после минимальности оставить N условий,
# равномерно по порядку перебора, пройти ими прежний конвейер вердиктов и записать
# статистику причин в form.census (статус схемы — «перепись», не результат).
SAMPLE = int(os.environ.get("ALGEN_SAMPLE", "0") or 0)
SAMPLE_EXAMPLES = int(os.environ.get("ALGEN_SAMPLE_EXAMPLES", "60") or 60)
EXAMPLE_MIN_SUPPORT = int(os.environ.get("ALGEN_EXAMPLE_MIN_SUPPORT", "0") or 0)
# Минимальность на месте (без второй копии условий); 0 — прежний путь с копией.
INPLACE_MINIMAL = os.environ.get("ALGEN_INPLACE_MINIMAL", "1") != "0"
REFRESH = 200  # выводов строк до пересоздания решателя
REDUCE = True  # сводить «неизвестно» к вопросу «посылки ⇒ переменная вырождена?»
# Посылки только из свойств (без отношений ⩽, ≅, ↪ между термами), начиная с этой
# глубины: для k = 3 отношения в посылках раздувают перебор, а задачи с ними — редкость.
PROPS_ONLY_FROM = 0
CLOSE_MARKED = True  # помеченные контрпримеры закрывают условия (см. run)
# Атомы, значение которых известно меньше чем в DEFER доле строк, откладываются:
# условия с ними — почти сплошь «неизвестно» (шум), а стоят решателя каждое.
# Они возвращаются в перебор, когда библиотека заполнится.
DEFER = 0.0
# Условия без посылок (k = 0) — часть класса k ⩽ 3: вопрос «всегда ли X?» не следует
# из вопросов «P ⇒ X» (проверщик 4.11: ЯЗ-43, ЯЗ-39). False — прежнее поведение.
ZERO_PREMISES = True
# При сжатии подсказки считаются только оставленным строкам (свёрнутым не нужны).
LATE_HINTS = True
# Строки таблицы: значения только атомов теории и столбцов формы (прочие ни на что не влияют).
ROW_FACT_FILTER = True
# Предел кэшей строк базы (записанные значения, выводы для разбора помеченных): строки G
# огромны, кэш общий для всех схем части — без предела память росла до гибели машины.
ROW_CACHE = 32
# Литералы-теоремы схемы ищутся и среди столбцов, где значение известно не во всех строках
# (ALGEN_FAST: строка — модель теории, но не все следствия выписаны). Литерал, выводимый
# из теории и посылок записи, верен в каждой строке, поэтому посылкой он лишний, а
# «опровержение» без него — настоящее (помощник 4.11: 261 вопрос пилота 9 держался на
# посылке-теореме с неизвестным значением). False — только столбцы, верные во всех строках.
THEORY_CONST = True
# Условие существования (req: атом о G/H имеет смысл при normal(H)) выполнено и
# литералом-теоремой из form.const: он посылкой не перебирается, и без этого
# все условия об атомах G/H, G/G′, G/Φ(G) терялись (проверщик 5.11).
REQ_CONST = True
# Semantic output version: paired premises now supply their primitive reqs.
# This is separate from Library/table caches and changes only paired runs.
PAIR_REQUIREMENTS_VERSION = 1

# Кэш вердиктов (состояние схемы для динамического архива). Вердикт условия
# зависит только от теории, не от библиотеки: при новой строке библиотеки схема
# перебирается заново, а решатель спрашивается только о новых условиях. VCACHE —
# прежние вердикты {ключ: (вид, ядро)}, VCACHE_OUT — все вопросы этого прогона
# (пишутся в состояние). None — кэша нет (прежнее поведение).
VCACHE = None
VCACHE_OUT = None
VCACHE_HITS = [0, 0]  # попадания, промахи

# Контрольный прежний путь для замеров. При пустом degen ответ всегда False;
# строить и хранить frozenset каждого запрета для этого ответа не нужно.
LEGACY_EMPTY_DEGEN_CACHE = os.environ.get("ALGEN_DEGEN_EMPTY_CACHE", "0") == "1"


def _h(text):
    """128-битный хэш строки (ключи кэша — числа: строки занимали память схемы;
    при 128 битах совпадение ключей на 10⁶ ключей схемы — около 10⁻²⁷)."""
    import hashlib
    return int.from_bytes(hashlib.blake2b(text.encode(), digest_size=16).digest(), "little", signed=True)


def _vkey(prem, goal):
    return _h(" ∧ ".join(sorted(lit_name(a, v) for a, v in prem)) + " ⊢ " + lit_name(*goal))


def cdecide(T, prem, goal, s):
    """decide через кэш вердиктов (VCACHE_OUT не None); иначе — просто decide."""
    if VCACHE_OUT is None:
        return decide(T, prem, goal, s)
    k = _vkey(prem, goal)
    hit = VCACHE.get(k) if VCACHE else None
    if hit is not None:
        kind, core = hit[0], hit[1]
        by = {_h(lit_name(a, v)): (a, v) for a, v in prem}
        ok = all(c in by for c in core)
        if ok and len(hit) > 2:
            # из выросшей теории: вывод верен, если посылки ещё совместны (иначе
            # теперь «противоречие» — спрашиваем решатель)
            ok = _joint_sat(T, prem, [], s) is True
        if ok:
            VCACHE_HITS[0] += 1
            VCACHE_OUT[k] = (kind, core)
            return Verdict(kind, [by[c] for c in core])
    VCACHE_HITS[1] += 1
    v = decide(T, prem, goal, s)
    VCACHE_OUT[k] = (v.kind, tuple(_h(lit_name(*x)) for x in v.core or []))
    return v


# Совместная проверка вместо цикла (ответы те же): если посылки вместе с
# отрицаниями ВСЕХ целей ds выполнимы, ни одна цель не выводится — модель
# годится каждой паре «посылки, ¬d». Иначе — прежний цикл по d. JOINT = False —
# только цикл.
JOINT = os.environ.get("ALGEN_JOINT", "1") == "1"


def _joint_sat(T, prem, extra, s):
    """Выполнимы ли посылки prem вместе с литералами extra ((атом, значение));
    None — не решить совместной проверкой (литерал-константа)."""
    lits = []
    for a, v in list(prem) + list(extra):
        l = T.lit(a, v)
        if l is None:
            continue
        if l is False:
            return None
        lits.append(l)
    key = _h("совместно: " + " ∧ ".join(sorted(lit_name(a, v) for a, v in list(prem) + list(extra))))
    hit = VCACHE.get(key) if VCACHE else None
    if hit is not None:
        if VCACHE_OUT is not None:
            VCACHE_OUT[key] = hit
        return hit[0] == "да"
    from . import fast
    ok = bool(fast.bank(T, s).sat(lits)[0])
    if VCACHE_OUT is not None:
        VCACHE_OUT[key] = ("да" if ok else "нет", ())
    return ok


def none_derivable(T, prem, ds, s):
    """Точно ли ни одно d из ds не выводится из prem (тогда цикл не нужен)."""
    if not JOINT or len(ds) < 2:
        return False
    for d in ds:
        if T.lit(*d) is None:  # цель-константа выводится из совместных посылок
            return False
    return _joint_sat(T, prem, [(a, not v) for a, v in ds], s) is True


def none_reduce(T, prem, goal, ds, s):
    """Точно ли ни при одном d из ds не выводится «prem ∧ ¬d ⊢ ¬goal»: выполнимо
    prem ∧ goal ∧ ¬d₁ ∧ … ∧ ¬dₙ."""
    if not JOINT or len(ds) < 2:
        return False
    if T.lit(*goal) is False:
        return False
    return _joint_sat(T, prem, [goal] + [(a, not v) for a, v in ds], s) is True

PACK_T = True  # pack по транспонированной m: те же слова, без транспонирования на каждый вызов
CORE_PROPS = {"trivial", "abelian", "cyclic", "finite", "fin-gen", "free", "simple", "solvable", "nilpotent",
              "perfect", "torsion-free", "periodic", "divisible", "centerless", "residually-finite",
              "indecomposable", "hopfian", "linear", "polycyclic", "bounded-exponent", "free-abelian", "p-group"}
CORE_SUB = {"normal", "characteristic", "maximal", "whole", "central", "finite-index", "complemented"}


# Полный класс по размеру (ALGEN_SIZE): у каждого терма — все свойства словаря его сорта
# (не только известные библиотеке и не только основные у построенных термов), вложения — между
# любыми группами одной схемы. Иначе перебор пропускает утверждения класса (сверка с архивом 3.11).
FULL_PROPS = bool(os.environ.get("ALGEN_SIZE"))

# Пары термов, между которыми заводятся отношения (None — все пары). При мере размера
# (ALGEN_SIZE) это пары из одной схемы: отношение термов разных схем не входит ни в одно
# перебираемое утверждение, а атомов таких пар — квадрат вселенной.
PAIR_FILTER = None


def relation_atoms(g, terms):
    if PAIR_FILTER is None:
        return _relation_atoms(g, terms)
    # только пары из одной схемы: идём по парам фильтра, а не по квадрату вселенной
    by = {str(t): t for t in terms}
    idx = {x: i for i, x in enumerate(by)}
    # порядок атомов — как у термов (не как у множества: у частей таблицы он должен совпадать)
    pairs = sorted(tuple(sorted(pr, key=idx.get)) for pr in PAIR_FILTER if all(x in idx for x in pr))
    pairs.sort(key=lambda p: (idx[p[0]], idx[p[1]]))
    out, seen = [], set()
    for x, y in pairs:
        if True:
            for a in _relation_atoms(g, [by[x], by[y]]):
                if a not in seen:
                    seen.add(a)
                    out.append(a)
    return out


def _relation_atoms(g, terms):
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
                    # сопряжённость и перестановочность — если одна из подгрупп переменная схемы
                    # (в полном классе, ALGEN_SIZE, — у всех пар: отбор пар делает PAIR_FILTER)
                    if FULL_PROPS or isinstance(a, Var) or isinstance(b, Var):
                        out += [("r", r, a, b) for r in ("conj-sub", "permutes") if r in g.v.rels]
    for i, a in enumerate(objs):
        for b in objs[i + 1:]:
            x, y = sorted((a, b), key=str)
            out.append(("r", "iso", x, y))
    # элементы одной группы: перестановочны, сопряжены, равны
    elts = [t for t in terms if g.terms[t].sort == "Grp.elt"]
    for i, a in enumerate(elts):
        for b in elts[i + 1:]:
            if g.terms[a].links.get("ambient") == g.terms[b].links.get("ambient"):
                x, y = sorted((a, b), key=str)
                out += [("r", r, x, y) for r in ("commute", "conjugate", "eq-elt") if r in g.v.rels]
    # числа: =, ⩽, делимость, взаимная простота
    nums = [t for t in terms if g.terms[t].sort == "Grp.num"]
    for a in nums:
        for b in nums:
            if a != b:
                out += [("r", r, a, b) for r in ("num-le", "num-divides") if r in g.v.rels]
                if str(a) < str(b):
                    out += [("r", r, a, b) for r in ("num-eq", "num-coprime") if r in g.v.rels]
    # вложение A ↪ B — только если одна из групп — переменная схемы (иначе пар слишком много)
    if "embeds" in g.v.rels:
        seen = set()
        for a in objs:
            for b in objs:
                # одна из групп — переменная схемы, или вложение структурное:
                # подгруппа в объемлющую, множитель в произведение (звенья транзитивности)
                if a != b and (FULL_PROPS or isinstance(a, Var) or isinstance(b, Var)
                               or g.terms[a].links.get("ambient") == b
                               or (isinstance(b, App) and b.op in ("prod", "freeprod", "wreath") and a in b.args)):
                    if (a, b) not in seen:
                        seen.add((a, b))
                        out.append(("r", "embeds", a, b))
    return out


def props():
    return [p for p in GROUP_PROPS if p not in SKIP]


def atom_name(a):
    return f"{a[1]}({', '.join(map(str, a[2:]))})"


_LIT_NAMES = {}


def lit_name(a, v):
    """Имя литерала; одна строка на литерал (у схемы G при k = 3 в отчёте до миллиона
    строк с этими именами — без общего экземпляра каждая занимала память заново)."""
    k = (a, v)
    n = _LIT_NAMES.get(k)
    if n is None:
        n = _LIT_NAMES[k] = ("" if v else "¬") + atom_name(a)
    return n


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
        out = set().union(*(term_vars(x) for x in a[2:] if not isinstance(x, (str, int, bool))))
        # отношения решётки подгрупп (⩽, =, сопряжённость, перестановочность) говорят и об
        # объемлющей группе: «H ≅ K ⇒ H, K сопряжены» — о G, H, K (проверщик: ЯЗ-37, ЯЗ-39)
        rel = graph.v.rels.get(a[1]) if hasattr(graph, "v") else None
        if rel and "Grp.sub" in (rel.get("in") or []):
            for x in a[2:]:
                info = graph.terms.get(x) if not isinstance(x, (str, int, bool)) else None
                amb = info.links.get("ambient") if info is not None else None
                if amb is not None:
                    out |= term_vars(amb)
        return out
    out = term_vars(a[2])
    if a[1] in SUB_PROPS:
        amb = graph.terms[a[2]].links.get("ambient")
        if amb is not None:
            out |= term_vars(amb)
    return out


# Сорта переменных, которые сами по себе ни о чём не говорят: морфизм — о своих
# группах, элемент и G-множество — об объемлющей группе, точка — о G-множестве.
# Условие о F: G → H касается и G, H (в меньшей базе его не записать).
DEPENDENT_SORTS = ("Grp.mor", "Grp.elt", "Grp.gset", "Grp.pt", "Grp.act")


def hidden_vars(graph):
    """Скрытые переменные записи: точка x_A G-множества A (etalon.scheme заводит её
    для правил о стабилизаторах). Условие не обязано её касаться."""
    out = set()
    for t, info in graph.terms.items():
        if isinstance(t, Var) and info.sort == "Grp.pt":
            amb = info.links.get("ambient")
            if amb is not None and str(t) == f"x_{amb}":
                out.add(t)
    return out


def dep_close(vs, graph):
    """Переменные vs и те, от которых зависят их сорта (DEPENDENT_SORTS)."""
    out, todo = set(vs), list(vs)
    while todo:
        v = todo.pop()
        info = graph.terms.get(v)
        if info is None or info.sort not in DEPENDENT_SORTS:
            continue
        for x in info.links.values():
            for u in term_vars(x):
                if u not in out:
                    out.add(u)
                    todo.append(u)
    return out


_AV = {}  # id графа → (граф, нужные переменные, кэш переменных атома с зависимостями)


def about_all_vars(lits, graph):
    """Условие (литералы посылок, цели и записи) говорит обо всех переменных базы,
    кроме скрытых, — с учётом зависимостей сортов. Иначе это утверждение меньшей
    базы (свойство N как группы — база G) и выдаётся там."""
    hit = _AV.get(id(graph))
    if hit is None or hit[0] is not graph:
        need = frozenset({t for t in graph.terms if isinstance(t, Var)} - hidden_vars(graph))
        hit = _AV[id(graph)] = (graph, need, {})
    _, need, memo = hit
    got = set()
    for a, _ in lits:
        vs = memo.get(a)
        if vs is None:
            vs = memo[a] = frozenset(dep_close(atom_vars(a, graph), graph))
        got |= vs
    return need <= got


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
    if a[0] == "r" and a[1] in SYMMETRIC:
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


_CANON = {}


def _canon_lit(a, v, i, perm):
    k = (a, v, i)
    n = _CANON.get(k)
    if n is None:
        n = _CANON[k] = ("" if v else "¬") + canon_atom(a, perm)
    return n


def klass(lits, perms):
    """Канонический запрет: множество литералов с точностью до симметрий."""
    if _CANON.get(("id",)) is not perms:  # кэш имён — для одного набора симметрий
        _CANON.clear()
        _CANON[("id",)] = perms
    return min(tuple(sorted(_canon_lit(a, v, i, perm) for a, v in lits))
               for i, perm in enumerate(perms))


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

    # Столбцы матриц битами (uint64 по строкам): строки, где верны литералы, — AND
    # слов, а не выборка столбцов из матрицы 30 тыс. × сотни на каждое условие.
    def _bits(self, mat):
        cache = self.__dict__.setdefault("_bitcache", {})
        hit = cache.get(id(mat))
        if hit is None or hit[0] is not mat:
            n = mat.shape[0]
            w = max(1, (n + 63) // 64)
            pk = np.packbits(mat, axis=0, bitorder="little")
            pad = np.zeros((w * 8 - pk.shape[0], mat.shape[1]), dtype=np.uint8)
            P = np.ascontiguousarray(np.vstack([pk, pad]).T).view(np.uint64)
            valid = np.packbits(np.arange(w * 64) < n, bitorder="little").view(np.uint64)
            hit = cache[id(mat)] = (mat, P, valid)
        return hit

    def _and(self, mat, cols):
        """Битовое множество строк mat, где верны все столбцы cols."""
        _, P, valid = self._bits(mat)
        R = valid.copy()
        for c in cols:
            R &= P[c]
        return R

    def _rows(self, mat, R):
        return np.flatnonzero(np.unpackbits(R.view(np.uint8), bitorder="little")[:mat.shape[0]])

    def unknown_goal(self, prem, g):
        """Строка, где посылки верны, а значение цели не записано и не
        выводится: заполнив его, можно закрыть условие. Записанные группы
        предпочтительнее построенных произведений."""
        _, P, _ = self._bits(self.m)
        rows = self._rows(self.m, self._and(self.m, list(prem) + self.fixed) & ~P[g] & ~P[g ^ 1])
        if not len(rows):
            return None
        real = rows[~self.synth_mask()[rows]]
        return int(real[0] if len(real) else rows[0])

    def synth_mask(self):
        """Строки построенных произведений (вычисляется один раз)."""
        if getattr(self, "_synth", None) is None or len(self._synth) != self.m.shape[0]:
            self._synth = np.array([self.synthetic(r) for r in range(self.m.shape[0])], dtype=bool)
        return self._synth

    def unknown_rows(self, prem, g):
        """Все строки, где посылки верны, а значение цели не записано и не выводится."""
        _, P, _ = self._bits(self.m)
        return self._rows(self.m, self._and(self.m, list(prem) + self.fixed) & ~P[g] & ~P[g ^ 1])

    def _image(self, r, t):
        """Образ терма t в строке r: ("obj", ключ) или ("sub", ключ, номер)."""
        key, sub = self.names[r]
        if t == self.sc.G:
            return ("obj", key)
        if t == self.sc.N:
            return ("sub", key, sub)
        q = self.lib.obj[key]["подгруппы"][sub].get("фактор")
        return ("obj", q) if q else None

    def one_unknown(self, cols, limit=None):
        """Строки, где ни один литерал запрета (столбцы cols) не ложен, а
        неизвестен ровно один: заполнив его, можно закрыть запрет.
        Возвращает [(строка, столбец неизвестного литерала)]."""
        # ответ зависит только от набора столбцов (неизвестен ровно один литерал),
        # а контрапозиции одного запрета спрашивают тот же набор
        mm = self.__dict__.get("_one_memo")
        if mm is None or mm[0] is not self.m:
            mm = self._one_memo = (self.m, {})
        memo = mm[1]
        key = (tuple(sorted(cols)), limit)
        hit = memo.get(key)
        if hit is None:
            hit = memo[key] = self._one_unknown(cols, limit)
        return list(hit)

    def _one_unknown(self, cols, limit=None):
        cols = list(cols) + self.fixed
        _, P, valid = self._bits(self.m)
        ok, one, two = valid.copy(), np.zeros_like(valid), np.zeros_like(valid)
        for c in cols:
            ok &= ~P[c ^ 1]  # ни один литерал не ложен
            u = ~P[c] & ~P[c ^ 1]
            two |= one & u
            one |= u
        rows = self._rows(self.m, ok & one & ~two)  # неизвестен ровно один
        if limit is not None and len(rows) > limit:
            real = rows[~self.synth_mask()[rows]]
            rows = np.concatenate([real, rows[self.synth_mask()[rows]]])[:limit]
        if len(rows):  # строк немного (limit): неизвестный литерал — по подматрице
            sub = self.m[rows]
            unk = ~sub[:, cols] & ~sub[:, [c ^ 1 for c in cols]]
            which = np.asarray(cols)[unk.argmax(axis=1)]
        else:
            which = []
        return list(zip(rows.tolist(), [int(c) for c in which]))

    def value_name(self, r, atom):
        cache = self.__dict__.setdefault("_vn", {})
        k = (int(r), atom)
        if k not in cache:
            cache[k] = self._value_name(r, atom)
        return cache[k]

    def _value_name(self, r, atom):
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
        if im is not None and im[0] not in ("obj", "sub"):  # гомоморфизм, семейство, действие, элемент…
            return f"{atom_name(atom)} у {self.where(r)}"
        if im is None and isinstance(t, App) and (t.op in FIELD_OF or t.op == "quotient"):
            # Не записана характеристическая подгруппа (центр, коммутант, Фраттини, кручение)
            # или фактор по ней: приписываем это группе, у которой её нет. Для G/N сначала
            # смотрим, есть ли образ N: иначе не записана сама N, а не фактор (прежде любой
            # G/N подписывался «не записан центр»).
            g = t.args[0]
            gim = self._image(r, g)
            if gim is not None and gim[0] == "obj":
                if t.op in FIELD_OF:
                    field = FIELD_OF[t.op]
                    what = MISSING[field]
                else:
                    n = t.args[1]
                    known = isinstance(n, App) and n.op in FIELD_OF
                    field = FIELD_OF[n.op] if known else None
                    if self._image(r, n) is None:
                        what = MISSING[field] if known else f"не записана подгруппа {n}"
                    else:
                        what = f"не записан фактор по {n}"
                key = base_factor(self.lib, gim[1], None, field)
                name = self.lib.obj[key].get('имя', key)
                return f"{what} у {name}"
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
        return self._rows(m, self._and(m, list(prem) + self.fixed + [neg]))

    def lit(self, j):
        """Номер столбца → (атом, значение)."""
        return self.atoms[j // 2], j % 2 == 0

    def lits(self, j):
        """Литералы столбца: у парного атома («P(A) и P(B)») — два литерала."""
        a = self.atoms[j // 2]
        if a[0] == "pair":
            _, p, x, y, pol = a
            return [(("p", p, x), pol), (("p", p, y), pol)]
        return [self.lit(j)]

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

    def deciding(self, prem, g, mark, limit=4):
        """На каких помеченных mark значениях держится опровержение условия.
        Для каждой из первых limit строк-опровержений (записанные группы
        раньше произведений) — наименьшие наборы помеченных значений, которых
        хватает. Возвращает {набор имён вида «hopfian(BS23)»: строка}."""
        mat = self.s if mark == "короткий довод" else self.m
        cols = list(prem) + self.fixed + [g ^ 1]
        rows = self.refuters(prem, g, mat)
        rows = np.concatenate([rows[~self.synth_mask()[rows]], rows[self.synth_mask()[rows]]])[:limit].tolist()
        out = {}
        for r in rows:
            named = dict(self.marked(r, mark))
            marked = sorted(named, key=str)
            hit = []
            # наборы до 2 значений (до 3 — только при немногих помеченных): каждый
            # набор — вывод решателем, а нужен лишь пример решающего факта для сводки
            for size in range(1, min(len(marked), 3 if len(marked) <= 6 else 2) + 1):
                hit = [k for k in combinations(marked, size)
                       if self.row_keeping(r, frozenset(k), mark)[cols].all()]
                if hit:
                    break
            for k in hit or [marked]:
                out.setdefault(frozenset(named[a] for a in k), r)
        return out


_NAMES = {}


def _atom_name_cached(a):
    n = _NAMES.get(a)
    if n is None:
        n = _NAMES[a] = atom_name(a)
    return n


_LITH = {}
_M128 = (1 << 128) - 1


def _lit_hash(a, v):
    k = (a, v)
    h = _LITH.get(k)
    if h is None:
        import hashlib
        name = f"{'' if v else '¬'}{_atom_name_cached(a)}"
        h = _LITH[k] = int.from_bytes(hashlib.blake2b(name.encode(), digest_size=16).digest(), "little")
    return h


def name_key(facts):
    """Ключ записанных значений строки по именам атомов — не зависит от нумерации
    переменных теории, поэтому годится между прогонами с разными правилами (A4).
    Сумма 128-битных хешей литералов: без сортировки строк на каждой строке таблицы
    (у G — сотни тысяч значений в строке)."""
    return f"{(sum(_lit_hash(a, v) for a, v in facts.items()) & _M128):032x}:{len(facts)}"


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
        from .deferred import make_search
        self.search = make_search(g, T, lib, constructor=Search)
        self.atoms = []
        for t in own:
            sort = g.terms[t].sort
            if FULL_PROPS:  # полный класс (ALGEN_SIZE): все свойства словаря, подходящие сорту терма
                self.atoms += [("p", p, t) for p in g.v.props if p not in SKIP and g.v.prop_fits(p, sort)]
                continue
            # у построенных термов — только основные свойства (арифметика порядка,
            # экспоненты, индексы — у переменных схемы): иначе шум растёт кратно
            ps = props() if isinstance(t, Var) else [p for p in props() if p in CORE_PROPS]
            sps = SUB_PROPS if isinstance(t, Var) else [p for p in SUB_PROPS if p in CORE_SUB]
            if sort == "Grp.obj":
                self.atoms += [("p", p, t) for p in ps]
            elif sort == "Grp.sub":
                self.atoms += [("p", p, t) for p in list(sps) + ps]
            elif sort == "Grp.mor":
                self.atoms += [("p", p, t) for p in MOR_PROPS]
            elif sort == "Grp.fam":
                self.atoms += [("p", p, t) for p in ps + ["finite-fam"] if g.v.prop_fits(p, sort)]
            elif sort == "Grp.elt":
                self.atoms += [("p", p, t) for p in ELT_PROPS if p in g.v.props]
            elif sort == "Grp.gset":
                self.atoms += [("p", p, t) for p in GSET_PROPS if p in g.v.props]
        if RELATIONS:
            self.atoms += relation_atoms(g, own)
        self.index = {a: i for i, a in enumerate(self.atoms)}
        self.req = {}
        for i, a in enumerate(self.atoms):
            need = {2 * self.index[("p", p, u)] for t in a[2:] if not isinstance(t, (str, int)) for p, u in g.requires(t) if ("p", p, u) in self.index}
            if need:
                self.req[i] = need
        self.fixed = [2 * self.index[a] + (0 if v else 1) for a, v in fixed if a in self.index]
        self.fixed_lits = fixed
        self.envs, self.skipped = [], []
        self._facts = {}  # записанные значения строк — лениво, только для разбора помеченных
        self._derived = {}  # кэш вывода: одинаковые наборы записанных значений — одна строка
        self.own = own
        if not with_rows:
            return
        self.fill_rows(part, max_subs)

    def fill_rows(self, part=None, max_subs=None):
        """Строки формы: подстановки библиотеки (part = (i, n) — каждая n-я)
        и выведенные значения атомов. Каркас (теория, атомы) уже построен —
        его можно строить один раз и раздавать частям через fork."""
        T = self.sc.T
        levels = {"m": (), "s": ("трудно",), "e": MARKS}
        rows, self.envs, self.skipped = {k: [] for k in levels}, [], []
        derived = self._derived
        self._used = used = set()  # ключи выводов, нужные этим строкам (для кэша между прогонами)
        for n_env, env in enumerate(self.search._assign(0, {})):
            if part and n_env % part[1] != part[0] - 1:
                continue
            if max_subs and any(im[0] == "sub" and im[2] >= max_subs for im in env.values()):
                continue
            facts, hard = self.search.facts(env)
            facts = self._relevant(facts)
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
                used.add(key)
                row = derived.get(key)
                if row is None:
                    nk = name_key(f)
                    self.__dict__.setdefault("_nk", {})[key] = nk
                    hints = self.__dict__.get("_hints")
                    row = derived[key] = self._derive(f, hints.get(nk) if hints else None)
                    # временные клаузы «хотя бы один меняет значение» копятся в
                    # решателе; свежий решатель через каждые REFRESH выводов
                    if REFRESH and len(derived) % REFRESH == 0:
                        self.sc.s.delete()
                        self.sc.s = T.solver()
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

    def _relevant(self, facts):
        """Значения только атомов формы и теории. Значения атомов, которых нет ни в
        клаузах теории, ни в столбцах формы, ни на что не влияют: свободная
        переменная в посылках решателя ничего не выводит, а значение строки берётся
        только у атомов формы. Прежде T.lit заводил их (у G — сотни тысяч на строку:
        память и время строки)."""
        if not ROW_FACT_FILTER:
            return facts
        T = self.sc.T
        keep = self.__dict__.get("_keep_set")
        if keep is None or keep[0] != (len(self.atoms), len(T.var)):
            # атомы формы и теории (симметричные отношения — в обоих порядках,
            # как их нормализует T.lit); один поиск в множестве на значение
            ks = set(self.atoms) | set(T.var)
            ks |= {(a[0], a[1], a[3], a[2]) for a in T.var if a[0] == "r" and a[1] in SYMMETRIC}
            keep = self._keep_set = ((len(self.atoms), len(T.var)), ks)
        ks = keep[1]
        return {a: v for a, v in facts.items() if a in ks}

    def row_facts(self, r):
        if r in getattr(self, "_live_rows", {}):
            return self._live_rows[r]["atom_facts"], {}
        if r not in self._facts:
            # кэш ограничен: у G записанных значений строки — сотни тысяч, а кэш
            # общий для всех схем части (база); без предела машина перебора пилота 9
            # умирала по памяти на 4-й схеме
            if len(self._facts) >= ROW_CACHE:
                self._facts.clear()
            facts, hard = self.search.facts(self.envs[r])
            self._facts[r] = (self._relevant(facts), hard)
        return self._facts[r]

    def _derive(self, facts, hint=None):
        """Значения атомов, следующие из записанных: ядро («backbone») решателя.
        Одна модель задаёт кандидата для каждого атома; атом проверяется одним
        вызовом, а атомы, которые разошлись с найденными моделями, — неизвестны.

        hint — значения, выведенные для этих же записанных значений прошлым
        прогоном с подмножеством нынешних правил (кэш по именам атомов, A4). Они
        следуют из записанных значений, поэтому берутся как посылки и не
        проверяются; ядро ищется только по остальным атомам. Если с ними теория
        противоречива (правило снято или исправлено), подсказка отбрасывается."""
        T, s = self.sc.T, self.sc.s
        assume = [l for a, v in facts.items() if (l := T.lit(a, v)) not in (None, False)]
        lit_of = self.__dict__.get("_lit_of")
        if lit_of is None or len(lit_of) != len(self.atoms):
            lit_of = self._lit_of = {a: T.lit(a) for a in self.atoms}
        lits = {a: l for a in self.atoms if a not in facts and type(l := lit_of[a]) is int}  # 1 == True: сравнивать нельзя
        val = {}
        if hint:
            extra = []
            for a, v in hint.items():
                l = lits.get(a)
                if l is not None:
                    extra.append(l if v else -l)
            if extra and s.solve(assumptions=assume + extra):
                for a, v in hint.items():
                    if a in lits:
                        val[a] = v
                        del lits[a]
                assume = assume + extra
        if FAST_DERIVE:
            ok, implied = s.propagate(assumptions=assume)
            if not ok:
                return [facts.get(a) for a in self.atoms]
            implied = set(implied or ())
            for a, l in lits.items():
                if l in implied:
                    val[a] = True
                elif -l in implied:
                    val[a] = False
            return [facts[a] if a in facts else val.get(a) for a in self.atoms]
        if not s.solve(assumptions=assume):
            return [facts.get(a) for a in self.atoms]
        model = s.get_model()
        # Единичное распространение даёт большую часть следствий почти даром.
        ok, implied = s.propagate(assumptions=assume)
        implied = set(implied or ())
        # Дальше — по номерам переменных и векторами numpy: модель решателя —
        # массив, без множеств из миллиона чисел на каждый вызов.
        V = np.array(sorted(set(lits.values())), dtype=np.int64)
        n = len(V)
        res = np.zeros(n, dtype=np.int8)  # 1 — верно, -1 — ложно, 0 — не выведено
        if n:
            imp = np.fromiter(implied, dtype=np.int64, count=len(implied))
            res[np.isin(V, imp)] = 1
            res[np.isin(-V, imp)] = -1
        act_m = res == 0  # ещё не решены
        st = np.zeros(n, dtype=bool)
        sf = np.zeros(n, dtype=bool)

        from operator import itemgetter
        get = itemgetter(*(V - 1).tolist()) if n > 1 else None

        def see(model):
            # из модели (список ±v длины «число переменных») — только наши переменные
            if n > 1 and len(model) >= V[-1]:
                pos = np.array(get(model), dtype=np.int64) > 0
                return pos, ~pos
            M = np.asarray(model, dtype=np.int64)
            pres = V <= len(M)
            idx = np.where(pres, V - 1, 0)
            pos = M[idx] > 0
            return pres & pos, pres & ~pos

        t, f_ = see(model)
        st |= t
        sf |= f_
        # Модели «наоборот»: решателю предлагаем противоположные значения всех
        # атомов, у которых пока одно значение, — одна модель снимает сразу многие.
        for _ in range(DIVERSE):
            one = act_m & (st != sf)
            if not one.any():
                break
            s.set_phases(np.where(st[one], -V[one], V[one]).tolist())
            if not s.solve(assumptions=assume):
                break
            t, f_ = see(s.get_model())
            new = one & ((st & f_) | (sf & t))
            st |= t & one
            sf |= f_ & one
            if not new.any():
                break
        # Остальные атомы с одним значением проверяем пачкой: временная клауза
        # «хотя бы один из них меняет значение». Модель снимает сразу многие;
        # противоречие — все оставшиеся выводятся.
        while True:
            one = act_m & (st != sf)
            if one.sum() < 3:
                break
            act = T.lit(("act", len(T.atoms)))
            flip = np.where(st[one], -V[one], V[one]).tolist()
            s.add_clause([-act] + flip)
            s.set_phases(flip)
            ok = s.solve(assumptions=assume + [act])
            mdl = s.get_model() if ok else None
            s.add_clause([-act])  # клауза больше не нужна
            if not ok:
                res[one] = np.where(st[one], 1, -1)
                act_m &= ~one
                break
            t, f_ = see(mdl)
            st |= t & one
            sf |= f_ & one
        for i in np.flatnonzero(act_m):
            if st[i] and sf[i]:
                continue
            v = int(V[i])
            if not st[i] and not sf[i]:
                # переменной нет в модели (решатель её не видел): две проверки
                if not s.solve(assumptions=assume + [-v]):
                    res[i] = 1
                elif not s.solve(assumptions=assume + [v]):
                    res[i] = -1
                continue
            want = bool(st[i])  # единственное пока значение
            if s.solve(assumptions=assume + [-v if want else v]):
                t, f_ = see(s.get_model())
                st |= t
                sf |= f_
            else:
                res[i] = 1 if want else -1
        by_var = {int(v): (r == 1) for v, r in zip(V, res) if r}
        for a, l in lits.items():
            if l in by_var:
                val[a] = by_var[l]
        return [facts[a] if a in facts else val.get(a) for a in self.atoms]

    def synthetic(self, r):
        if r in getattr(self, "_live_rows", {}):
            return False
        return any(im[0] == "obj" and self.lib.obj[im[1]].get("синтез") for im in self.envs[r].values())

    def _image(self, r, t):
        if r in getattr(self, "_live_rows", {}):
            return None
        return self.search._image(t, self.envs[r])

    def where(self, r):
        if r in getattr(self, "_live_rows", {}):
            packet = self._live_rows[r]
            return packet["source"].get("where") or (packet["key"] + ": " + str(packet["assignment"]))
        return self.where_env(self.envs[r])

    def where_env(self, env):
        return ", ".join(f"{t} = {self.search._name(im)}" for t, im in env.items())

    def marked(self, r, mark):
        _, hard = self.row_facts(r)
        return sorted(((a, name) for a, (m, name) in hard.items() if m == mark), key=lambda x: str(x[0]))

    def row_keeping(self, r, keep, mark):
        if r in getattr(self, "_live_rows", {}):
            return self.m[r]
        k = (r, keep, mark)
        base = getattr(self, "_base", None)
        if base is not None and k not in self._kept:
            # схема-вид: строка выводится один раз по атомам базы (кэш базы общий
            # для всех схем), отсюда берутся столбцы схемы
            self._kept[k] = base.row_keeping(r, keep, mark)[self._base_cols]
        if k not in self._kept:
            facts, hard = self.row_facts(r)
            drop = ("трудно",) if mark == "трудно" else MARKS
            f = {a: v for a, v in facts.items() if not (a in hard and hard[a][0] in drop and a not in keep)}
            key = self._key(f)
            row = self._derived.get(key)
            if row is None:
                if base is None and len(self._derived) >= ROW_CACHE:
                    self._derived.clear()  # кэш базы (общий для схем): с пределом, см. row_facts
                row = self._derived[key] = self._derive(f)
            if base is None and len(self._kept) >= 4 * ROW_CACHE:
                self._kept.clear()
            self._kept[k] = self._matrix([row])[0]
        return self._kept[k]


def _unknowns(o):
    """Сколько у записи не хватает: незаписанные свойства, центр, коммутант."""
    return (sum(o["свойства"].get(p) is None for p in GROUP_PROPS)
            + (o.get("центр") is None) + (o.get("коммутант") is None))


# Поля записи группы библиотеки для характеристических подгрупп (подсказки «не записан …»).
FIELD_OF = {"center": "центр", "commutator": "коммутант", "frattini": "фраттини", "torsion": "кручение"}
MISSING = {"центр": "не записан центр", "коммутант": "не записан коммутант",
           "фраттини": "не записана подгруппа Фраттини", "кручение": "не записано кручение"}


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
        if not ua:
            return key  # у обоих множителей поле есть — не записано у самого произведения
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


def add_pairs(form, pairs):
    """Парные атомы для симметричных переменных (A, B): «P(A) и P(B)» и
    «¬P(A) и ¬P(B)». Столбец 0 — оба верны, столбец 1 — хотя бы один ложен.
    В посылках берётся только столбец 0, целью парный атом не бывает: так
    условия вида «A, B к. п. и ф. а. ⇒ …» укладываются в меньшее k."""
    if getattr(form, "pair_atoms", None):
        return
    index = {a: i for i, a in enumerate(form.atoms)}
    new_atoms, cols = [], {k: [] for k in "mse"}
    comp = {}
    for x, y in pairs:
        for a in list(form.atoms):
            if a[0] != "p" or a[2] != x or ("p", a[1], y) not in index:
                continue
            ia, ib = index[a], index[("p", a[1], y)]
            for pol in (True, False):
                d = 0 if pol else 1
                pa = ("pair", a[1], x, y, pol)
                for k in "mse":
                    mat = getattr(form, k)
                    both = mat[:, 2 * ia + d] & mat[:, 2 * ib + d]
                    notboth = mat[:, 2 * ia + 1 - d] | mat[:, 2 * ib + 1 - d]
                    cols[k] += [both, notboth]
                comp[len(form.atoms) + len(new_atoms)] = {ia, ib}
                new_atoms.append(pa)
    if not new_atoms:
        return
    base = len(form.atoms)
    for k in "mse":
        setattr(form, k, np.hstack([getattr(form, k), np.stack(cols[k], axis=1)]))
    form.atoms = list(form.atoms) + new_atoms
    if hasattr(form, "index"):
        form.index = {a: i for i, a in enumerate(form.atoms)}
    for i, cs in comp.items():
        r = set().union(*(form.req.get(c, set()) for c in cs))
        if r:
            form.req[i] = r
    if getattr(form, "need", None):
        form.need = [grp | {i for i, cs in comp.items() if cs & grp} for grp in form.need]
    form.pair_atoms = comp  # номер парного атома → номера атомов-составляющих
    form._synth = None


# Конструкции-свидетели («существует группа, в которую …»): терм — выбор, свойства его не определены.
WITNESS = {"hnn-hull", "higman-hull", "free-cover", "free-cover-map"}


def pair_requirement_providers(form):
    """Only the positive column of a pair supplies its signed constituents.

    The other column means NOT(both), not two negated constituents. Synthetic
    numeric test forms without atom descriptors have no logical expansion.
    """
    pairs = getattr(form, "pair_atoms", None) or {}
    atoms = getattr(form, "atoms", None)
    if not pairs or atoms is None:
        return {}
    index = {a: i for i, a in enumerate(atoms)}
    out = {}
    for i, components in pairs.items():
        if not 0 <= i < len(atoms) or atoms[i][0] != "pair":
            raise ValueError("pair metadata does not match atom descriptors")
        _, p, x, y, pol = atoms[i]
        ids = (index[("p", p, x)], index[("p", p, y)])
        if set(ids) != set(components):
            raise ValueError("pair components do not match atom descriptors")
        out[2 * i] = tuple(2 * c + (0 if pol else 1) for c in ids)
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
    # Литералы-теоремы схемы (верны во всех строках и выводятся без посылок,
    # например Inn(G) ↪ Aut(G)): как цель — факт без посылок, как посылка — лишние.
    const = set()
    if hasattr(form, "sc") and hasattr(form.sc, "T"):
        fixed_l = [form.lit(j) for j in form.fixed]
        if THEORY_CONST and m.shape[0]:
            # кандидаты: ни в одной строке записи литерал не ложен (строки — модели)
            rf = m[:, list(form.fixed)].all(axis=1) if form.fixed else np.ones(m.shape[0], dtype=bool)
            neg = m[rf].any(axis=0)
            cand = [j for j in range(n_lit) if not neg[j ^ 1]]
        else:
            cand = np.flatnonzero(m.all(axis=0)).tolist()
        for j in cand:
            if int(j) in form.fixed:
                continue
            if cdecide(form.sc.T, fixed_l, form.lit(int(j)), form.sc.s).kind == "выводится":
                const.add(int(j))
    # Замкнутые числовые литералы (2 ⩽ 3, 6 = 2 · 3, простое ли 7): значение — арифметика,
    # одно во всех строках; ни посылкой, ни целью они не нужны.
    def ground(t):
        return isinstance(t, App) and all(ground(a) for a in t.args)
    for i, a in enumerate(getattr(form, "atoms", None) or []):
        if all(ground(x) for x in a[2:] if not isinstance(x, (str, int))) and any(
                isinstance(x, App) and form.g.terms.get(x) is not None and form.g.terms[x].sort == "Grp.num"
                for x in a[2:]):
            for j in (2 * i, 2 * i + 1):
                if m.shape[0] and m[:, j].all():
                    const.add(j)
    form.const = sorted(const)
    providers = pair_requirement_providers(form)

    def supplied(columns):
        have = set(columns)
        have.update(c for j in columns for c in providers.get(j, ()))
        return have

    have0 = supplied(set(form.fixed) | (const if REQ_CONST else set()))

    def have_columns(prem):
        return supplied(prem) | have0
    # атом посылки записи (класс базы, ALGEN_CLASS) целью не бывает: его значение задано
    fixed_atoms = {j // 2 for j in getattr(form, "fixed", [])}
    if fixed_atoms:
        goal_cols = [g for g in goal_cols if g // 2 not in fixed_atoms]
    if const:
        goal_cols = [g for g in goal_cols if g not in const and g ^ 1 not in const]
    # Отложенные атомы: известны меньше чем в DEFER доле строк (кроме посылок записи).
    deferred = set()
    if DEFER > 0 and m.shape[0]:
        frac = (m[:, 0::2] | m[:, 1::2]).mean(axis=0)
        keep = {j // 2 for j in getattr(form, "fixed", [])}
        deferred = {i for i in np.flatnonzero(frac < DEFER).tolist() if i not in keep}
    form.deferred = sorted(atom_name(form.atoms[i]) for i in deferred)
    # Не перебираются ни посылкой, ни целью: атомы о замкнутых термах (abelian(A(5)) —
    # факт библиотеки, а не теорема о переменных базы) и о свидетелях (hnn-hull(G),
    # higman-hull(G), free-cover(G) — выбор, а не функция: nilpotent(hnn-hull(G)) не определён).
    def _has(t, ops):
        return isinstance(t, App) and (t.op in ops or any(_has(x, ops) for x in t.args))
    for i, a in enumerate(getattr(form, "atoms", None) or []):
        ts = [x for x in a[2:] if not isinstance(x, (str, int, bool))]
        if ts and (all(ground(x) for x in ts) or any(_has(x, WITNESS) for x in ts)):
            deferred.add(i)
    if deferred:
        goal_cols = [g for g in goal_cols if g // 2 not in deferred]
    pairs = getattr(form, "pair_atoms", None) or {}
    if pairs:
        goal_cols = [g for g in goal_cols if g // 2 not in pairs]
    # равносильные литералы (table.drop_equiv): перебираются только представители
    drop = getattr(form, "drop", None) or set()
    if drop:
        goal_cols = [g for g in goal_cols if g not in drop]
    # атомы, несовместимые в одной посылке с данным (парный и его составляющие)
    clash = {}
    for i, cs in pairs.items():
        clash.setdefault(i, set()).update(cs)
        for c in cs:
            clash.setdefault(c, set()).add(i)
    for i, cs in pairs.items():  # «P(A) и P(B)» с «¬P(A) и ¬P(B)» — тоже
        clash[i] |= {k for k, ds in pairs.items() if ds == cs}
    # Произвольный список целей может быть неупорядочен; прежний путь остаётся
    # и для него, и для кодов, которым нужно больше 64 бит. Класс не сужается.
    alive = {}
    if PACKED_CONDITIONS and goals is None and max_prem >= 0:
        try:
            alive = PackedConditions(n_lit, max_prem, m.shape[0])
        except OverflowError:
            pass
    empty, lower = [], set()
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

    direct_memo, rows_memo, Pall = {}, {}, None

    def alive_direct(q, g):
        """Подусловие (q, g) не опровергнуто (для минимальности при покрытии)."""
        have = have_columns(q)
        if not all(form.req.get(j // 2, set()) <= have for j in list(q) + [g]):
            return False
        key = (q, g)
        hit = direct_memo.get(key)
        if hit is not None:
            return hit
        R = rows_memo.get(q)
        if R is None:
            nonlocal Pall
            if Pall is None:
                Pall = pack(every)  # столбцы по всем строкам, битами
            R = Pall[q[0]].copy()
            for j in q[1:]:
                R &= Pall[j]
            R = rows_memo[q] = R if R.any() else None
        hit = direct_memo[key] = R is not None and not (R & Pall[g ^ 1]).any()
        return hit

    # Столбцы как битовые множества строк (uint64): пересечение посылок и
    # проверка «есть ли строка, где посылки верны, а цель ложна» — по словам,
    # без копирования подматрицы (у GN — 143 тыс. строк × 348 литералов).
    nr = m.shape[0]
    neg_idx = np.arange(n_lit) ^ 1
    bufs = {}

    mT = None  # m по столбцам (n_lit, строк) — для pack без транспонирования

    def pack(rows):
        """Столбцы по строкам rows (номера строк m) — матрица (n_lit, слов)."""
        nonlocal mT
        w = max(1, (len(rows) + 63) // 64)
        if not PACK_T:
            pk = np.packbits(m[rows], axis=0, bitorder="little")
            pad = np.zeros((w * 8 - pk.shape[0], n_lit), dtype=np.uint8)
            return np.ascontiguousarray(np.vstack([pk, pad]).T).view(np.uint64)
        if mT is None:
            mT = np.ascontiguousarray(m.T)
        out = np.zeros((n_lit, w * 8), dtype=np.uint8)
        pk = np.packbits(mT[:, rows], axis=1, bitorder="little")
        out[:, :pk.shape[1]] = pk
        return out.view(np.uint64)

    def ones(n):
        mask = np.zeros(max(1, (n + 63) // 64) * 64, dtype=bool)
        mask[:n] = True
        return np.packbits(mask, bitorder="little").view(np.uint64)

    # Лист перебора векторами по всем целям сразу (VEC): те же проверки, что в цикле
    # по целям ниже, и та же минимальность — «lower» хранит для набора q маску целей,
    # прошедших проверки листа, alive_direct — маску по всем строкам. Порядок целей
    # (по возрастанию) и счётчик — те же.
    n_atoms = n_lit // 2
    goal_static = np.zeros(n_lit, dtype=bool)
    goal_static[list(goal_cols)] = True
    req_goals = {g: form.req[g // 2] for g in range(n_lit) if form.req.get(g // 2)}
    lower_vec, direct_vec, subset_bits = {}, {}, {}

    def goal_bits(mask):
        return int.from_bytes(np.packbits(mask, bitorder="little").tobytes(), "little")

    def req_ok(have):
        ok = np.ones(n_lit, dtype=bool)
        for g, rq in req_goals.items():
            if not rq <= have:
                ok[g] = False
        return ok

    def direct_mask(q):
        """alive_direct(q, g) для всех g сразу."""
        hit = direct_vec.get(q)
        if hit is not None:
            return hit
        have = have_columns(q)
        if not all(form.req.get(j // 2, set()) <= have for j in q):
            d = np.zeros(n_lit, dtype=bool)
        else:
            nonlocal Pall
            if Pall is None:
                Pall = pack(every)
            R = Pall[q[0]].copy()
            for j in q[1:]:
                R &= Pall[j]
            if not R.any():
                d = np.zeros(n_lit, dtype=bool)
            else:
                d = ~(Pall & R).any(axis=1)[neg_idx] & req_ok(have)
        direct_vec[q] = d
        return d

    def eligible_goals(atoms, have, gc):
        if gc is goal_cols:
            m = goal_static.copy()
        else:  # то же, что np.isin(np.arange(n_lit), gc), без сортировки
            m = np.zeros(n_lit, dtype=bool)
            m[np.asarray(gc, dtype=np.intp)] = True
        for a in atoms:
            m[2 * a] = m[2 * a + 1] = False
        if req_goals:
            m &= req_ok(have)
        if pairs:
            for g in np.flatnonzero(m):
                if clash.get(int(g) // 2, set()) & atoms:
                    m[g] = False
        return m

    def leaf_vec(prem, atoms, have, gc, negs, buf, depth, eligible=None, P=None, R=None):
        nonlocal count
        m = (eligible if eligible is not None else eligible_goals(atoms, have, gc)) & ~negs
        n = int(m.sum())
        if not n:
            if depth < max_prem:
                lower_vec[tuple(prem)] = m
            return
        count += n
        tp = tuple(prem)
        if depth < max_prem:
            lower_vec[tp] = m
        if EARLY_MIN:
            left = goal_bits(m)
            for q in proper_subsets(prem):
                b = subset_bits.get(q)
                if b is None:
                    d = direct_mask(q) if need else lower_vec.get(q)
                    b = subset_bits[q] = 0 if d is None else goal_bits(d)
                left &= ~b
                if not left:
                    return
            while left:
                bit = left & -left
                g = bit.bit_length() - 1
                alive[(tp, g)] = int(np.bitwise_count(P[g] & R if buf is None else buf[g]).sum())
                left ^= bit
            return
        sub = np.zeros(n_lit, dtype=bool)
        for q in proper_subsets(prem):
            if need:
                sub |= direct_mask(q)
            else:
                x = lower_vec.get(q)
                if x is not None:
                    sub |= x
        for g in np.flatnonzero(m & ~sub).tolist():
            alive[(tp, g)] = int(np.bitwise_count(P[g] & R if buf is None else buf[g]).sum())

    def go(prem, R, start, depth, pm, P, rows_map):
        nonlocal count
        if need:
            miss = full & ~pm
            if bin(miss).count("1") > 2 * (depth - len(prem) + 1):
                return  # не хватит литералов, чтобы коснуться всех элементов
        if len(prem) == depth:
            atoms = {j // 2 for j in prem}
            have = have_columns(prem)
            if not all(form.req.get(i, set()) <= have for i in atoms):
                return
            if not R.any():
                empty.append(tuple(prem))
                return
            gc = goal_cols
            if need:
                miss = full & ~pm
                ok = (lmask & miss) == miss
                gc = [g for g in goal_cols if ok[g]]
                if not gc:
                    return
            eligible = None
            if vec and SPARSE_LEAF:
                eligible = eligible_goals(atoms, have, gc)
                cols = np.flatnonzero(eligible)
                if not len(cols):
                    if depth < max_prem:
                        lower_vec[tuple(prem)] = eligible
                    return
                if len(cols) * 4 < n_lit:
                    negs = np.zeros(n_lit, dtype=bool)
                    negs[cols] = (P[cols ^ 1] & R).any(axis=1)
                    leaf_vec(prem, atoms, have, gc, negs, None, depth, eligible, P, R)
                    return
            buf = bufs.get(P.shape)
            if buf is None:
                buf = bufs[P.shape] = np.empty(P.shape, dtype=np.uint64)
            np.bitwise_and(P, R, out=buf)
            hits = buf.any(axis=1)  # литерал верен хотя бы в одной строке посылок
            negs = hits[neg_idx]
            if vec:
                leaf_vec(prem, atoms, have, gc, negs, buf, depth, eligible)
                return
            for g in gc:
                if g // 2 in atoms or not form.req.get(g // 2, set()) <= have:
                    continue
                if pairs and clash.get(g // 2, set()) & atoms:
                    continue
                if negs[g]:
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
                alive[key] = int(np.bitwise_count(buf[g]).sum())
            return
        if prem:
            if not R.any():
                return  # посылки уже несовместны в библиотеке: продолжения — тоже
            # Строк посылок мало — сжать матрицу до них: всё поддерево работает
            # с короткими строками битов (k = 3: тройки — по строкам пары).
            n_on = int(np.bitwise_count(R).sum())
            if n_on * 4 < len(rows_map) and P.shape[1] > 4:
                bits = np.unpackbits(R.view(np.uint8), bitorder="little")[:len(rows_map)].astype(bool)
                rows_map = rows_map[bits]
                P, R = pack(rows_map), ones(len(rows_map))
        used = {x // 2 for x in prem}
        for j in range(start, n_lit):
            if j // 2 in used or j in const or j ^ 1 in const or j // 2 in deferred or j in drop:
                continue
            # Свободные множества: литерал j верен во всех строках посылок — набор с
            # ним и все его продолжения имеют те же строки, что и без j, поэтому все
            # их неопровергнутые условия неминимальны (без j тоже не опровергнуты).
            # Такие наборы вверх замкнуты, так что у оставшихся все подмножества
            # тоже остались. Не для j, нужного как условие существования терма.
            if prune and prem and j not in reqcols and not (R & ~P[j]).any():
                continue
            if pairs and ((j // 2 in pairs and j % 2) or clash.get(j // 2, set()) & used):
                continue
            if PROPS_ONLY_FROM and len(prem) + 1 >= PROPS_ONLY_FROM and form.atoms[j // 2][0] == "r":
                continue
            go(prem + [j], P[j] & R, j + 1, depth, pm | (int(lmask[j]) if need else 0), P, rows_map)

    reqcols = set().union(*form.req.values()) if form.req else set()
    reqcols |= {j for j, supplied_cols in providers.items() if reqcols.intersection(supplied_cols)}
    vec = VEC and goals is None
    prune = PRUNE_FREE and not form.fixed  # alive_direct смотрит все строки, а не строки записи
    start = np.flatnonzero(m[:, form.fixed].all(axis=1)) if form.fixed else np.arange(nr)
    P0 = pack(start)
    native = None
    form.enumeration_engine = "python"
    if NATIVE_ENUM and vec and isinstance(alive, PackedConditions) and 0 <= max_prem <= 3:
        from .native_enum import enumerate_numeric
        skip = np.array([j in const or j ^ 1 in const or j // 2 in deferred or j in drop
                         or (j // 2 in pairs and j % 2) for j in range(n_lit)], dtype=np.uint8)
        fixed_mask = np.array([j in have0 for j in range(n_lit)], dtype=np.uint8)
        req_mask = np.array([j in reqcols for j in range(n_lit)], dtype=np.uint8)
        relation = np.array([PROPS_ONLY_FROM and form.atoms[a][0] == "r"
                             for a in range(n_atoms)], dtype=np.uint8)
        all_rows = P0 if not form.fixed else pack(every)
        native = enumerate_numeric(alive, P0, all_rows, len(start), goal_static, skip, fixed_mask,
                                   form.req, req_mask, clash, lmask if need else np.zeros(n_lit, dtype=np.uint64),
                                   full if need else 0, prune, relation, PROPS_ONLY_FROM, providers=providers)
    if native is None:
        for depth in range(1, max_prem + 1):
            go([], ones(len(start)), 0, depth, 0, P0, start)
    else:
        alive, empty, count, engine_hash = native
        form.enumeration_engine = "cpp:" + engine_hash
    if ZERO_PREMISES:
        # Условия без посылок: цель, не опровергнутая ни одной строкой (записи), — вопрос
        # «всегда ли X?» (выводимые без посылок — form.const — исключены из целей и
        # выписываются фактами). Базис должен его содержать: из «P ⇒ X» он не следует.
        # ((), X) выдаётся, если X касается всех верхних термов схемы (иначе — в меньшей
        # схеме). Условия «P ⇒ X» не снимаются: доказуемое «P ⇒ X» — факт, а не следствие
        # вопроса «X?»; невыводимое сжатие свернёт в «X?» (следует из него).
        fixed_set = have0
        zero = {g for g in goal_cols
                if form.req.get(g // 2, set()) <= fixed_set and not m[start, g ^ 1].any()}
        if zero:
            for g in sorted(zero):
                if not need or int(amask[g // 2]) == full:
                    alive[((), g)] = len(start)
    form.n_alive = count
    return alive, empty


def minimal(alive, inplace=False):
    """Оставить условия, у которых без любой посылки цель опровергается.

    inplace=True: результат пишется в те же массивы `alive` и возвращается сам
    `alive` (без второй копии условий); ключи/поддержки/порядок те же.
    """
    if inplace and isinstance(alive, PackedConditions):
        if NATIVE_MINIMAL and INPLACE_MINIMAL:
            from .native_enum import minimal_inplace
            if minimal_inplace(alive) is not None:
                return alive
        out = minimal(alive)
        alive.blocks, alive.size = out.blocks, out.size
        return alive
    if NATIVE_MINIMAL and isinstance(alive, PackedConditions):
        from .native_enum import minimal_packed
        result = minimal_packed(alive)
        if result is not None:
            return result
    out = empty_like(alive)
    for (prem, g), support in alive.items():
        if all((tuple(x for x in prem if x != p), g) not in alive for p in prem if len(prem) > 1):
            out[prem, g] = support
    return out


def pair_minimal(form, mins):
    """Условия с парной посылкой «P(A) и P(B)»: минимальность и по литералам —
    если без одной половины пары цель всё ещё не опровергается, условие не
    минимально («A тривиальна и A, B абелевы ⇒ …» — хватает «B абелева»)."""
    m, pairs = form.m, form.pair_atoms
    req = getattr(form, "req", {})
    have0 = set(form.fixed) | (set(getattr(form, "const", ())) if REQ_CONST else set())
    out = empty_like(mins)
    for (prem, g), sup in mins.items():
        if not any(j // 2 in pairs for j in prem):
            out[prem, g] = sup
            continue
        cols = []
        for j in prem:
            if j // 2 in pairs:
                _, p, x, y, pol = form.atoms[j // 2]
                cols += [2 * form.index[("p", p, x)] + (0 if pol else 1),
                         2 * form.index[("p", p, y)] + (0 if pol else 1)]
            else:
                cols.append(j)
        cols += list(form.fixed)
        redundant = False
        for c in set(cols) - set(form.fixed):
            rest = [x for x in cols if x != c]
            have = set(rest) | have0
            if any(not req.get(j // 2, set()) <= have for j in rest + [g]):
                continue  # removing this literal makes a remaining term undefined
            rows = m[:, rest].all(axis=1) if rest else np.ones(m.shape[0], dtype=bool)
            if rows.any() and not m[rows, g ^ 1].any():
                redundant = True
                break
        if not redundant:
            out[prem, g] = sup
    form.n_pair_dropped = len(mins) - len(out)
    return out


def generic_filter(form, mins):
    """Условие только о свойствах одного терма t (не переменной) — по сути
    условие о группах вообще. Оставляем его в схеме терма, только если общая
    версия (t → произвольная группа базы G) опровергается библиотекой: значит,
    условие держится на устройстве t («Inn(G) циклична ⇒ тривиальна»). Иначе
    это повтор базы G (там оно и выдаётся) или общая теорема."""
    gen = getattr(form, "generic", None)
    if gen is None or os.environ.get("ALGEN_COMPRESS"):
        return mins  # при сжатии экземпляры сворачивает compress.instances со ссылкой
    gm, gcol = gen  # матрица базы G и {свойство: номер атома}
    # Класс прогона (ALGEN_CLASS, «∀ G конечная» и т. п.): общая версия R0
    # спрашивается в базе G только для групп класса. Условие о t снимается,
    # только если теория выводит, что t в классе; иначе R(t) держится на R0
    # для групп вне класса, которое нигде не спрашивается (дыра 4.11).
    cls = os.environ.get("ALGEN_CLASS", "")
    in_class = {}

    def class_ok(t):
        if not cls:
            return True
        if t not in in_class:
            T = form.sc.T
            s = T.solver()
            try:
                in_class[t] = decide(T, list(getattr(form, "fixed_lits", [])), (("p", cls, t), True), s).kind == "выводится"
            finally:
                s.delete()
        return in_class[t]

    out, dropped = empty_like(mins), 0
    form.generic_kept_class = 0
    for (prem, g), sup in mins.items():
        lits = [l for j in prem for l in form.lits(j)] + [form.lit(g)]
        ts = {a[2] for a, _ in lits}
        t = next(iter(ts))
        if len(ts) != 1 or any(a[0] != "p" for a, _ in lits) or isinstance(t, Var) \
                or any(a[1] not in gcol for a, _ in lits):
            out[prem, g] = sup
            continue
        cols = [2 * gcol[a[1]] + (0 if v else 1) for a, v in lits[:-1]]
        a, v = lits[-1]
        neg = 2 * gcol[a[1]] + (1 if v else 0)
        if gm[:, cols + [neg]].all(axis=1).any():
            out[prem, g] = sup  # общая версия опровергается — условие о терме
        elif not class_ok(t):
            out[prem, g] = sup  # t не доказуемо в классе: R0 вне класса не спрашивается
            form.generic_kept_class += 1
        else:
            dropped += 1
    form.n_generic = dropped
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
    # вырождения для сведения остатка: группа тривиальна, подгруппа тривиальна или вся
    degen_all = []
    for t in sorted(allvars, key=str):
        sort = graph.terms[t].sort
        if sort == "Grp.obj":
            degen_all.append((("p", "trivial", t), True))
        elif sort == "Grp.sub":
            degen_all += [(("p", "trivial", t), True), (("p", "whole", t), True)]
    degen_all = [d for d in degen_all if form.sc.T.lit(d[0]) is not None] if REDUCE else []
    if getattr(form, "pairs", None):
        # парные атомы — поправка 2 класса: при сбое схема падает со статусом «ошибка»,
        # а не перебирается молча без поправки (проверщик 4.11, №13)
        add_pairs(form, form.pairs)
    # Контрпример с помеченным значением («трудно», «короткий довод») закрывает
    # условие: нетривиален сам контрпример, он записан в библиотеке и идёт в
    # архив один раз, а не с каждым условием, которое опровергает (решение Димы
    # 1.11.2026). CLOSE_MARKED = False — прежнее поведение с корзинами.
    form.mem = []  # (этап, VmRSS ГБ, сколько записей) — где схема набирает память

    def _mem(stage, n):
        try:
            with open("/proc/self/status") as status:
                rss = next(int(x.split()[1]) / 1e6 for x in status if x.startswith("VmRSS"))
        except (OSError, StopIteration):
            rss = None
        form.mem.append((stage, None if rss is None else round(rss, 2), n))
    _mem("начало", 0)
    alive, empty = enumerate_form(form, max_prem, m=form.m if CLOSE_MARKED else None)
    _mem("перебор", len(alive))
    mins = minimal(alive, inplace=True)  # alive дальше не нужен: run возвращает те же массивы
    _mem("минимальные", len(mins))
    if getattr(form, "pair_atoms", None):
        mins = pair_minimal(form, mins)
    mins = generic_filter(form, mins)
    sample_total = None
    if SAMPLE and not CENSUS and len(mins) > SAMPLE:
        sample_total = len(mins)
        step = len(mins) / SAMPLE
        want, picked = sorted({int(i * step) for i in range(SAMPLE)}), empty_like(mins)
        if isinstance(mins, PackedConditions):
            # по индексу, без обхода сотен миллионов условий в Python
            base, j = 0, 0
            for n, (keys, values) in mins.blocks.items():
                while j < len(want) and want[j] < base + len(keys):
                    code, sup = keys[want[j] - base], values[want[j] - base]
                    goal = code & mins.mask
                    code >>= mins.width
                    prem = []
                    for _ in range(n):
                        prem.append(code & mins.mask)
                        code >>= mins.width
                    picked[tuple(reversed(prem)), goal] = int(sup)
                    j += 1
                base += len(keys)
        else:
            wanted = set(want)
            for i, (key, sup) in enumerate(mins.items()):
                if i in wanted:
                    picked[key] = sup
        mins = picked
    if CENSUS:
        # Перепись объёма: только перебор и минимальность, без вердиктов. Отчёт пуст
        # и результатом схемы не является (сводка помечена полем «перепись»).
        blocks = getattr(mins, "blocks", None)
        form.census = {"минимальных": len(mins), "пустых посылок": len(empty),
                       "не опровергнуто": getattr(form, "n_alive", None),
                       "по длине": ({str(d): len(k) for d, (k, _) in blocks.items()} if blocks is not None else None),
                       "движок": getattr(form, "enumeration_engine", None)}
        return form, mins, empty, []
    report, degen_memo = [], {}
    late_hints = bool(os.environ.get("ALGEN_COMPRESS")) and LATE_HINTS
    for (prem, g), support in mins.items():
        prem_l = [l for j in prem for l in form.lits(j)]
        goal = form.lit(g)
        # Условие только о части переменных — факт меньшей схемы.
        if not about_all_vars(prem_l + [goal] + fixed, graph):
            continue
        # Вырожденное: посылки заставляют группу быть тривиальной или
        # подгруппу — тривиальной или всей. Это тоже факт меньшей схемы.
        # Смотрим на весь запрет, чтобы контрапозиции решались одинаково.
        if degen or LEGACY_EMPTY_DEGEN_CACHE:
            whole = fixed + prem_l + [(goal[0], not goal[1])]
            # Один ответ на весь запрет (у контрапозиций тот же набор литералов).
            wkey = frozenset(whole)
            dg = degen_memo.get(wkey)
            if dg is None:
                dg = degen_memo[wkey] = (not none_derivable(form.sc.T, whole, degen, form.sc.s)
                                         and any(cdecide(form.sc.T, whole, d, form.sc.s).kind == "выводится"
                                                 for d in degen))
            if dg:
                continue
        v = cdecide(form.sc.T, fixed + prem_l, goal, form.sc.s)
        r = {"_cols": list(prem) + [g ^ 1],
             "посылки": [lit_name(*x) for x in prem_l], "цель": lit_name(*goal),
             "запрет": sorted([lit_name(*x) for x in prem_l] + [lit_name(goal[0], not goal[1])]),
             "класс": klass(prem_l + [(goal[0], not goal[1])], perms),
             "примеров": support, "вердикт": v.kind,
             "ядро": [lit_name(*x) for x in v.core or []]}
        if v.kind == "неизвестно" and late_hints:
            r["_hint"] = (prem, g, prem_l, goal)
        elif v.kind == "неизвестно":
            hint = form.unknown_goal(prem, g)
            if hint is not None:
                r["заполнить"] = {"где": form.where(hint), "атом": atom_name(goal[0])}
            # Решающие значения: строки, где неизвестен ровно один литерал запрета.
            # Сведение к вырожденности: если посылки вместе с «v нетривиальна» уже
            # дают отрицание цели, вопрос условия — «посылки ⇒ v тривиальна?»
            # (десятки «третьих» вида ¬abelian(G ∗ G), ¬cyclic(G ∗ G)… — один вопрос).
            for d in ([] if none_reduce(form.sc.T, fixed + prem_l, goal, degen_all, form.sc.s) else degen_all):
                if cdecide(form.sc.T, fixed + prem_l + [(d[0], not d[1])], (goal[0], not goal[1]),
                          form.sc.s).kind == "выводится":
                    r["сводится"] = sorted(lit_name(*x) for x in prem_l) + [lit_name(*d)]
                    break
            r["значения"] = sorted({form.value_name(x, form.lit(c)[0]) if form.lit(c)[0][0] != "pair" else
                                    form.value_name(x, form.lits(c)[0][0])
                                    for x, c in form.one_unknown(list(prem) + [g ^ 1], limit=60)})
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
    if not late_hints:
        questions(form, report)
    # Сжатие выдачи (тред «Сжать выдачу», py/algen/compress.py): только добавляет
    # поля строкам, без флага выдача прежняя бит в бит.
    _mem("вердикты", len(report))
    if os.environ.get("ALGEN_COMPRESS"):
        from algen import compress
        compress.compress(form, report)
        _mem("сжатие", len(report))
    if late_hints:
        # Подсказки (решающие значения, сведение к вырожденности, вопрос «какие группы
        # с S») — только оставленным после сжатия: свёрнутым они не нужны (вопрос
        # разбирается по базису), а это ≈ треть времени схемы. Вердикты и сжатие от
        # подсказок не зависят.
        for r in report:
            h = r.pop("_hint", None)
            if h is None or r.get("свёрнута"):
                continue
            prem, g, prem_l, goal = h
            hint = form.unknown_goal(prem, g)
            if hint is not None:
                r["заполнить"] = {"где": form.where(hint), "атом": atom_name(goal[0])}
            for d in ([] if none_reduce(form.sc.T, fixed + prem_l, goal, degen_all, form.sc.s) else degen_all):
                if cdecide(form.sc.T, fixed + prem_l + [(d[0], not d[1])], (goal[0], not goal[1]),
                          form.sc.s).kind == "выводится":
                    r["сводится"] = sorted(lit_name(*x) for x in prem_l) + [lit_name(*d)]
                    break
            r["значения"] = sorted({form.value_name(x, form.lit(c)[0]) if form.lit(c)[0][0] != "pair" else
                                    form.value_name(x, form.lits(c)[0][0])
                                    for x, c in form.one_unknown(list(prem) + [g ^ 1], limit=60)})
        questions(form, [r for r in report if not r.get("свёрнута")])
    if SAMPLE and not CENSUS:
        form.census = _sample_stats(form, mins, report, sample_total)
    for r in report:
        r.pop("_cols", None)
    return form, alive, empty, report


def _sample_stats(form, mins, report, total):
    """Состав выборки: вердикты, отсеянные до отчёта, и для неизвестных — держится
    ли запрет на одном неизвестном значении таблицы (и каком атоме)."""
    from collections import Counter
    kinds, blocked, atoms, reduce = Counter(r["вердикт"] for r in report), 0, Counter(), 0
    for r in report:
        if r["вердикт"] != "неизвестно":
            continue
        reduce += bool(r.get("сводится"))
        cols = r.get("_cols") or []
        hits = form.one_unknown(cols, limit=60) if cols else []
        if hits:
            blocked += 1
            names = set()
            for _, c in hits:
                for a, _v in form.lits(c):
                    names.add(atom_name(a))
            atoms.update(names)
    # диагностика: живые примеры и доля неизвестных значений решающих атомов
    examples, atom_col = [], {}
    import numpy as np
    _, P, valid = form._bits(form.m)
    nrows = form.m.shape[0]
    synth = form.synth_mask()

    def unpack(bits):
        return np.unpackbits(bits.view(np.uint8), bitorder="little")[:nrows].astype(bool)
    for r in report:
        if r["вердикт"] != "неизвестно":
            continue
        cols = r.get("_cols") or []
        hits = form.one_unknown(cols, limit=60) if cols else []
        for _, c in hits:
            for a, _v in form.lits(c):
                atom_col.setdefault(atom_name(a), c)
        if len(examples) < SAMPLE_EXAMPLES and not EXAMPLE_MIN_SUPPORT:
            prem, g = cols[:-1], cols[-1] ^ 1
            sat = form._and(form.m, list(prem) + list(form.fixed))
            n_sat = int(unpack(sat).sum())
            n_true = int(unpack(sat & P[g]).sum())
            n_unk = int(unpack(sat & ~P[g] & ~P[g ^ 1]).sum())
            examples.append({"посылки": r["посылки"], "цель": r["цель"], "строк с посылками": n_sat,
                             "цель верна": n_true, "цель неизвестна": n_unk,
                             "из них синтетических": int((unpack(sat & ~P[g] & ~P[g ^ 1]) & synth).sum()),
                             "решающие": [form.value_name(x, form.lit(c)[0]) if form.lit(c)[0][0] != "pair" else
                                          form.value_name(x, form.lits(c)[0][0]) for x, c in hits[:3]]})
    if EXAMPLE_MIN_SUPPORT:
        # кандидаты в правила: цель верна во ВСЕХ строках с посылками, строк ⩾ порога
        for r in report:
            if r["вердикт"] != "неизвестно" or len(examples) >= SAMPLE_EXAMPLES:
                continue
            cols = r.get("_cols") or []
            prem, g = cols[:-1], cols[-1] ^ 1
            sat = form._and(form.m, list(prem) + list(form.fixed))
            n_sat = int(unpack(sat).sum())
            if n_sat < EXAMPLE_MIN_SUPPORT:
                continue
            n_true = int(unpack(sat & P[g]).sum())
            if n_true != n_sat:
                continue
            examples.append({"посылки": r["посылки"], "цель": r["цель"], "строк с посылками": n_sat,
                             "настоящих": int((unpack(sat) & ~synth).sum())})
    unknown_share = {}
    for name, _cnt in atoms.most_common(40):
        c = atom_col.get(name)
        if c is None:
            continue
        unk = unpack(valid & ~P[c] & ~P[c ^ 1])
        unknown_share[name] = {"настоящих строк": int((~synth).sum()), "неизвестно у настоящих": int((unk & ~synth).sum()),
                               "синтетических строк": int(synth.sum()), "неизвестно у синтетических": int((unk & synth).sum())}
    return {"примеры": examples, "доля неизвестных": unknown_share,
            "минимальных": total if total is not None else len(mins), "выборка": len(mins),
            "в отчёте": len(report), "отсеяно до отчёта": len(mins) - len(report),
            "вердикты": dict(kinds), "неизвестно на одном значении": blocked,
            "сводится к вырожденности": reduce, "решающие атомы": atoms.most_common(40)}


# Вопрос запрета: наименьшее подмножество S его литералов, которому в библиотеке
# удовлетворяют не больше QUESTION_ROWS групп. Запрет тогда держится на том, что
# известных групп с S мало: вопрос «какие группы бывают с S?» закрывает разом все
# запреты с этим S (правилом «S ⇒ …» или новой группой). Для одного S таких
# запретов десятки, и S повторяется во многих схемах базы — сводка их складывает.
QUESTION_ROWS = 10


def questions(form, report, limit=None):
    limit = QUESTION_ROWS if limit is None else limit
    if not limit:
        return
    m = form.m
    _, P, _ = form._bits(m)  # столбцы битами: AND слов вместо выборки столбцов
    base = form._and(m, form.fixed)
    cache = {}

    def rows(S):
        if S not in cache:
            R = base.copy()
            for j in S:
                R &= P[j]
            cache[S] = form._rows(m, R)
        return cache[S]

    done = {}  # у контрапозиций запрета тот же набор F — тот же вопрос
    for r in report:
        if r["вердикт"] != "неизвестно" or "_cols" not in r:
            continue
        F = tuple(sorted(r["_cols"]))
        if F in done:
            if done[F] is not None:
                r["вопрос"] = {k: list(v) if isinstance(v, list) else v for k, v in done[F].items()}
            continue
        done[F] = None
        for size in range(1, len(F)):
            cand = [(len(rows(S)), S) for S in combinations(F, size) if len(rows(S)) <= limit]
            if cand:
                n, S = min(cand)
                names = sorted(lit_name(*l) for j in S for l in form.lits(j))
                # строки, где S не опровергнуто, но и не известно: много таких —
                # вопрос скорее о незаписанных значениях (правило вроде «linear(G) ⇒
                # linear(G ∗ G)»), чем о редкости групп с S
                maybe = base.copy()
                for j in S:
                    maybe &= ~P[j ^ 1]
                r["вопрос"] = {"S": " & ".join(names), "групп": n, "неизвестно": int(np.bitwise_count(maybe).sum()) - n,
                               "группы": [form.where(int(x)) for x in rows(S)[:3]],
                               "все группы": sorted(form.where(int(x)) for x in rows(S))}
                done[F] = {k: list(v) if isinstance(v, list) else v for k, v in r["вопрос"].items()}
                break


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
    if getattr(form, "n_generic", 0):
        print(f"убрано условий об одном терме, верных или открытых для всех групп (их место — база G): {form.n_generic}",
              file=sys.stderr)
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
    reduced = {}
    # Сжатие (ALGEN_COMPRESS, py/algen/compress.py): свёрнутый вопрос следует из
    # теории и оставленных вопросов. Он не выкидывается, а показывается свёрнутым
    # со ссылками «следует из №…» и возвращается, если источник опровергнут.
    folded = {}
    for r in report:
        if r["вердикт"] != "неизвестно":
            continue
        if r.get("свёрнута"):
            folded[r["№"]] = r
            continue
        t = r["класс"]
        seen.setdefault(t, r["примеров"])
        if r.get("сводится"):
            reduced.setdefault(t, tuple(r["сводится"]))
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
    # Сведённые к вырожденности: один вопрос «посылки ⇒ вырождено?» на много запретов.
    red = defaultdict(list)
    for t in bare_fresh:
        if t in reduced:
            red[reduced[t]].append(t)
    bare_fresh = [t for t in bare_fresh if t not in reduced]
    print(f"== сводятся к вырожденности: {len(red)} вопросов на {sum(len(ts) for ts in red.values())} запретов ==")
    for q, ts in sorted(red.items(), key=lambda x: (-len(x[1]), x[0])):
        print(f"вырождено? {' & '.join(q[:-1])} ⇒ {q[-1]}   [запретов {len(ts)}]")
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
    if folded:
        print(f"== свёрнуто вопросов {len(folded)}: следуют из теории и оставленных вопросов ==")
        for k, r in sorted(folded.items()) if full else ():
            print(f"№{k} {' & '.join(r['класс'])} ⇐ " + ", ".join(f"№{d}" for d in r["следует из"]))
        print(f"свёрнуто вопросов {len(folded)} (список: --полностью)", file=sys.stderr)
    summary = {
        "запретов": len(classes), "вердикты": dict(tally), "остаток": len(seen),
        "значения": [{"имя": v, "запретов": len(ts), "пример": " & ".join(ts[0])} for v, ts in fresh],
        "без кандидата": [{"пара": list(pair), "третьи": thirds} for pair, thirds in cl],
        "вырождено": [{"вопрос": list(q), "запретов": len(ts)} for q, ts in red.items()],
        "реестр": {k: len(ts) for k, ts in known.items()},
        "отложено": getattr(form, "deferred", []),
    }
    if any("сжатие" in r for r in report):  # без флага сводка прежняя бит в бит
        summary["свёрнуто"] = {k: r["следует из"] for k, r in folded.items()}
        from algen import compress
        summary["оставленные вопросы"] = compress.kept_questions(report)  # для сжатия между схемами
        # Полный список для архива: базис фактов (свёрнутые факты следуют из него без
        # теории) и условия, опровергнутые только помеченным значением библиотеки.
        kept_f, seen_f = [], set()
        for r in report:
            if r["вердикт"] == "выводится" and not r.get("свёрнута") and r.get("№") not in seen_f:
                seen_f.add(r.get("№"))
                kept_f.append({"№": r.get("№"), "посылки": r["посылки"], "цель": r["цель"], "ядро": r.get("ядро", [])})
        summary["оставленные факты"] = kept_f
        summary["свёрнуто фактов"] = sum(1 for r in report if r["вердикт"] == "выводится" and r.get("свёрнута"))
    # Факты без посылок: литералы-теоремы схемы (выводятся без посылок), касающиеся
    # каждого верхнего терма (так каждый попадает ровно в одну схему); замкнутые
    # числовые (2 ⩽ 3) — арифметика, не выписываются.
    need = getattr(form, "need", None) or []
    def _ground(t):
        return isinstance(t, App) and all(_ground(a) for a in t.args)
    summary["факты без посылок"] = sorted(
        lit_name(*form.lit(j)) for j in getattr(form, "const", [])
        if form.atoms[j // 2][0] != "pair" and all(j // 2 in n for n in need)
        and not all(_ground(x) for x in form.atoms[j // 2][2:] if not isinstance(x, (str, int, bool))))
    qs = {}
    for r in classes.values():
        q = r.get("вопрос")
        if r["вердикт"] != "неизвестно" or not q:
            continue
        x = qs.setdefault(q["S"], {"запретов": 0, "групп": q["групп"], "неизвестно": q.get("неизвестно"), "группы": q["группы"],
                                   "все группы": q.get("все группы"), "пример": " & ".join(r["запрет"])})
        x["запретов"] += 1
    summary["вопросы"] = qs
    summary["без вопроса"] = sum(1 for r in classes.values() if r["вердикт"] == "неизвестно" and not r.get("вопрос"))
    print(f"вопросов «какие группы бывают с S»: {len(qs)} на {sum(x['запретов'] for x in qs.values())} запретов; "
          f"без вопроса {summary['без вопроса']}", file=sys.stderr)
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
    if getattr(form, "census", None) is not None:
        print("ПЕРЕПИСЬ (ALGEN_CENSUS=1): вердиктов нет, это не результат схемы: "
              + json.dumps(form.census, ensure_ascii=False), file=sys.stderr)
    render(form, alive, empty, report, short=a.short, full=a.full, json_path=a.out)


if __name__ == "__main__":
    main()
