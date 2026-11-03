"""Таблицы баз: значения всех атомов над вселенной термов на всех строках
библиотеки — считаются один раз, а схемы берут из них столбцы.

База — переменные (G; G и N ⩽ G; A, B; …). Вселенная базы — все термы глубины 1
над её переменными (Z(G), G′, G/N, A × B, …) и отобранные термы глубины 2.
Схема — замкнутый (с подтермами) набор не больше чем из k + 1 термов вселенной.
Условие выдаётся ровно в одной схеме: той, что порождена термами, которых оно
касается. Поэтому одно и то же условие не повторяется в разных схемах.

    cd py
    python3 -m algen.table вселенная GN                      # термы вселенной
    python3 -m algen.table схемы GN                          # схемы базы
    python3 -m algen.table строить GN --часть 3/20 --каталог ../кэш/табл
    python3 -m algen.table перебор GN --каталог ../кэш/табл --выход ../кэш/прогон --часть 1/4
"""

import argparse
import io
import json
import signal
import multiprocessing as mp
import os
import pickle
import sys
import time
import traceback
from itertools import combinations, product
from pathlib import Path

import numpy as np

from . import enumerate as E
from .etalon import scheme, term
from .library import _fingerprint, built_library
from .logic import App, Var, Vocab

BASES = {
    "G": "∀ G : Grp",
    "GN": "∀ G : Grp; ∀ N : Sub(G)",
    "AB": "∀ A : Grp; ∀ B : Grp",
    "GHK": "∀ G : Grp; ∀ H : Sub(G); ∀ K : Sub(G)",
    "GMN": "∀ G : Grp; ∀ M : Sub(G); ∀ N : Sub(M)",
    "GHF": "∀ G : Grp; ∀ H : Grp; ∀ F : Mor(G, H)",
    "Fam": "∀ F : Fam",
    # новые сорта: действие (со скрытой точкой x_A), элемент, эндоморфизм
    # (два элемента «Gxy» — позже: пар классов слишком много для таблицы)
    "GX": "∀ G : Grp; ∀ A : GSet(G)",
    "Gx": "∀ G : Grp; ∀ x : Elt(G)",
    "GE": "∀ G : Grp; ∀ F : Mor(G, G)",
    "GXxy": "∀ G : Grp; ∀ A : GSet(G); ∀ x, y : Pt(A)",
    "Gxy": "∀ G : Grp; ∀ x, y : Elt(G)",
    "D": "∀ D : Diag",
    "MN": "∀ m, n : Num",
    "ABH": "∀ A : Grp; ∀ B : Grp; ∀ H : Sub(A ∗ B)",
    "ABC": "∀ A : Grp; ∀ B : Grp; ∀ C : Grp",
    # числа-параметры: семейства S(n), D(n), группы порядка p q, p^k, …
    "n": "∀ n : Num",
    "pG": "∀ p : Num; ∀ G : Grp",
    "pqG": "∀ p, q : Num; ∀ G : Grp",
    "pGH": "∀ p : Num; ∀ G : Grp; ∀ H : Sub(G)",
    "pqGH": "∀ p, q : Num; ∀ G : Grp; ∀ H : Sub(G)",
    # 2.11: остальные объявления с n ⩽ 3 (полнота по n; перечень — все сорта Grp, Num, Sub, Elt, GSet, Mor, Pt)
    "GxA": "∀ G : Grp; ∀ x : Elt(G); ∀ A : GSet(G)",
    "GxF": "∀ G : Grp; ∀ x : Elt(G); ∀ F : Mor(G, G)",
    "GAB": "∀ G : Grp; ∀ A : GSet(G); ∀ B : GSet(G)",
    "GAF": "∀ G : Grp; ∀ A : GSet(G); ∀ F : Mor(G, G)",
    "GAa": "∀ G : Grp; ∀ A : GSet(G); ∀ a : Pt(A)",
    "GHx": "∀ G : Grp; ∀ H : Grp; ∀ x : Elt(G)",
    "GHA": "∀ G : Grp; ∀ H : Grp; ∀ A : GSet(G)",
    "GHE": "∀ G : Grp; ∀ H : Grp; ∀ F : Mor(G, G)",
    "GHn": "∀ G : Grp; ∀ H : Grp; ∀ n : Num",
    "GHK2": "∀ G : Grp; ∀ H : Grp; ∀ K : Sub(G)",
    "GFE": "∀ G : Grp; ∀ F : Mor(G, G); ∀ E : Mor(G, G)",
    "Gnx": "∀ G : Grp; ∀ n : Num; ∀ x : Elt(G)",
    "GnA": "∀ G : Grp; ∀ n : Num; ∀ A : GSet(G)",
    "GnF": "∀ G : Grp; ∀ n : Num; ∀ F : Mor(G, G)",
    "GNx": "∀ G : Grp; ∀ N : Sub(G); ∀ x : Elt(G)",
    "GNy": "∀ G : Grp; ∀ N : Sub(G); ∀ x : Elt(N)",
    "GNA": "∀ G : Grp; ∀ N : Sub(G); ∀ A : GSet(G)",
    "GNF": "∀ G : Grp; ∀ N : Sub(G); ∀ F : Mor(G, G)",
    "lmn": "∀ l, m, n : Num",
}
NEW_N = ["GxA", "GxF", "GAB", "GAF", "GAa", "GHx", "GHA", "GHE", "GHn", "GHK2", "GFE", "Gnx", "GnA", "GnF",
         "GNx", "GNy", "GNA", "GNF", "lmn"]

# Конструкции вселенной (термы-«вершины» схем).
CONS = ["center", "commutator", "ab", "aut", "inn", "quotient", "prod", "freeprod", "wreath",
        "meet", "join", "normalizer", "centralizer", "normal-closure", "ker", "im", "torsion", "frattini", "prod-fam", "sum-fam",
        "stab", "act-ker", "gen", "centralizer-elt"]
SYMMETRIC = {"prod", "freeprod"}            # A × B ≅ B × A: берём один порядок
SYMMETRIC_SUB = {"meet", "join"}            # meet(G, H, K) = meet(G, K, H)

# Термы глубины 2, известные по задачам (подтермы добавляются сами).
DEPTH2 = {
    "G": ["commutator(commutator(commutator(G)))", "comm(G, commutator(G), whole-sub(G))",
          "meet(G, center(G), commutator(G))", "join(G, center(G), commutator(G))",
          "meet(G, center(G), frattini(G))", "meet(G, commutator(G), frattini(G))",
          "centralizer(G, commutator(G))", "centralizer(G, frattini(G))",
          "aut(center(G))", "aut(commutator(G))", "ab(commutator(G))", "frattini(commutator(G))",
          "center(frattini(G))", "aut(ab(G))", "center(aut(G))", "commutator(aut(G))",
          "commutator(G / center(G))", "frattini(G / frattini(G))", "torsion(ab(G))",
          "center(commutator(G))", "commutator(commutator(G))", "G / center(G)",
          "center(G / center(G))", "G / commutator(G)", "aut(G) / inn(G)",
          "G / frattini(G)"],
    "AB": ["center(A × B)", "commutator(A × B)"],
    "GMN": ["M / N", "G / M", "normal-closure(M, N)"],
    "GHF": ["G / ker(F)"],
    "Fam": ["center(prod-fam(F))", "commutator(prod-fam(F))", "prod-fam(F) / sum-fam(F)"],
}


# Базы, у которых вселенная — только термы задач архива и DEPTH2, без всех
# конструкций глубины 1 (у ABH их 69: 4851 атом — таблица не нужна такая)
ARCHIVE_ONLY = {"ABH", "ABC", "n", "pG", "pqG", "pGH", "pqGH", "MN"}


# Мера полноты по размеру (решение 2–3.11): ALGEN_SIZE=s — вселенная базы есть все
# термы из ⩽ s конструкций (а не глубина ⩽ 2 по выбору), схемы — наборы термов
# с ⩽ s конструкциями вместе. Без переменной окружения — прежняя вселенная.
SIZE = int(os.environ.get("ALGEN_SIZE", "0") or 0)


# Поправка 3 (класс по архиву): фактор по своей каноничной подгруппе — G/Z(G), G/G′,
# Aut G/Inn G — одна конструкция, а не две.
CANON_SUB = {"center", "commutator", "inn", "torsion", "frattini", "ulm"}


def app_nodes(t):
    """Конструкции терма (узлы-применения, без числовых констант)."""
    out = set()
    if isinstance(t, App):
        if t.args or not str(t.op).startswith("num:"):
            out.add(t)
        args = t.args
        if t.op == "quotient" and len(args) == 2 and isinstance(args[1], App) and args[1].op in CANON_SUB:
            args = (args[0],) + tuple(args[1].args)
        for a in args:
            out |= app_nodes(a)
    return out


def size_universe(vocab, base, smax):
    """Все термы базы из ⩽ smax конструкций CONS (по возрастанию размера), с замыканием."""
    g, _, _ = scheme(vocab, {"раздел": "grp", "условие": BASES[base]})
    vars_ = [t for t in g.terms if isinstance(t, Var)]
    allt, sz = list(vars_), {t: 0 for t in vars_}
    # раунды до неподвижной точки: G/Z(G) — размер 1, но строится из Z(G) (поправка 3)
    nodes = {t: frozenset() for t in vars_}
    fresh = set(vars_)
    for _round in range(2 * smax):
        prev = list(allt)
        new = set()
        # аргумент терма из ⩽ smax конструкций сам из ⩽ smax − 1 (кроме c(Y) в Y/c(Y))
        small = [t for t in prev if len(nodes[t]) < smax]
        canon = [t for t in prev if isinstance(t, App) and t.op in CANON_SUB and len(nodes[t]) <= smax]
        for op in CONS:
            c = vocab.cons.get(op)
            if not c:
                continue
            pools = [small] * len(c["in"])
            if op == "quotient":
                pools = [small, small + [t for t in canon if t not in small]]
            for args in product(*pools):
                if not fresh.intersection(args):
                    continue  # такой набор аргументов уже пробовали в прошлом раунде
                if op in SYMMETRIC and str(args[0]) > str(args[1]):
                    continue
                if op in SYMMETRIC_SUB and not str(args[1]) < str(args[2]):
                    continue
                if op == "quotient" and isinstance(args[1], App) and args[1].op in CANON_SUB:
                    n = len(nodes[args[0]] | set().union(*(app_nodes(a) for a in args[1].args))) + 1
                else:
                    n = len(frozenset().union(*(nodes[a] for a in args))) + 1
                if n > smax:
                    continue
                try:
                    t = g.make(op, list(args))
                except Exception:
                    t = None
                if t is not None and t not in sz:
                    nodes[t] = frozenset(app_nodes(t))
                    sz[t] = len(nodes[t])
                    new.add(t)
                    allt.append(t)
        if not new:
            break
        fresh = new
    allt.sort(key=lambda t: sz[t])
    out = [t for t in allt if isinstance(t, App)]
    for t in list(out):
        for x in closure(g, [t] + vars_):
            if isinstance(x, App) and x not in out:
                out.append(x)
    return [str(t) for t in out]


def universe(vocab, base):
    """Термы вселенной базы (строки) в порядке построения."""
    if SIZE:
        return size_universe(vocab, base, SIZE)
    g, _, _ = scheme(vocab, {"раздел": "grp", "условие": BASES[base]})
    vars_ = list(g.terms)
    out = []
    for op in (() if base in ARCHIVE_ONLY else CONS):
        c = vocab.cons.get(op)
        if not c:
            continue
        for args in product(vars_, repeat=len(c["in"])):
            if op in SYMMETRIC and str(args[0]) > str(args[1]):
                continue
            if op in SYMMETRIC_SUB and not str(args[1]) < str(args[2]):
                continue
            t = g.make(op, list(args))
            if t is not None and t not in out:
                out.append(t)
    names = {str(t): t for t in g.terms}
    for x in DEPTH2.get(base, []) + archive_terms(vocab, base):
        t = term(g, x, names, "grp")
        for s in subterms(t):
            if isinstance(s, App) and s not in out:
                out.append(s)
    # термы замыкания (область, кообласть: profinite-map(G) ⇒ profinite(G)) — тоже во вселенной
    for t in list(out):
        for s in closure(g, [t] + [v for v in g.terms if isinstance(v, Var)]):
            if isinstance(s, App) and s not in out:
                out.append(s)
    return [str(t) for t in out]


_ARCHIVE = {}


def archive_terms(vocab, base):
    """Термы карточек архива (data/archive/grp), переменные которых — переменные базы
    (после переименования): вселенная базы содержит все термы её задач."""
    if base in _ARCHIVE:
        return _ARCHIVE[base]
    from itertools import permutations
    from .coverage import cards, shape, _rename, _sub, variants
    from .logic import DATA
    _, bvs, _, _ = shape(vocab, BASES[base])
    out = []
    for c in (x for _f, c0 in cards(DATA / "archive" / "grp") for x in variants(c0)):
        if not c.get("условие") or not c.get("цель"):
            continue
        try:
            g, prem, goal = scheme(vocab, {"раздел": "grp", "условие": c["условие"], "цель": c["цель"]})
        except Exception:
            continue
        vs = [(t.name, g.terms[t].sort, {k: str(v) for k, v in g.terms[t].links.items()})
              for t in g.terms if isinstance(t, Var)]
        if len(vs) != len(bvs):
            continue
        used = set()
        for at, _v in prem + [goal]:
            for x in at[2:]:
                if isinstance(x, App):
                    used |= {y for y in _sub(x) if isinstance(y, App)}
        for perm in permutations(range(len(bvs))):
            ren = {vs[i][0]: bvs[perm[i]][0] for i in range(len(vs))}
            if all(vs[i][1] == bvs[perm[i]][1] and
                   {k: ren.get(v, v) for k, v in vs[i][2].items()} == bvs[perm[i]][2] for i in range(len(vs))):
                out += [_rename(t, ren) for t in sorted(used, key=str) if _rename(t, ren) not in out]
                break
    _ARCHIVE[base] = out
    return out


def subterms(t):
    """Подтермы t, включая сам t, снизу вверх."""
    out = []
    if isinstance(t, App):
        for a in t.args:
            for s in subterms(a):
                if s not in out:
                    out.append(s)
    out.append(t)
    return out


def closure(g, elems):
    """Замыкание набора: подтермы и связи (объемлющая группа, области F)."""
    out, todo = set(), list(elems)
    while todo:
        t = todo.pop()
        if t in out:
            continue
        out.add(t)
        if isinstance(t, App):
            todo += list(t.args)
        todo += [v for v in g.terms[t].links.values() if v is not None]
    return out


def maximal(g, elems):
    """Верхние элементы: не подтермы и не связи других элементов набора."""
    low = set()
    for t in elems:
        low |= closure(g, [t]) - {t}
    return [t for t in elems if t not in low]


# Симметрии баз: перестановка переменных, переводящая запись базы в себя.
# Поправка 2: P(A) и P(B) для симметричных переменных — одна посылка (парные атомы)
SWAP = {"AB": ("A", "B"), "GHK": ("H", "K"), "MN": ("m", "n"), "Gxy": ("x", "y"),
        "GFE": ("F", "E"), "pqG": ("p", "q"), "pqGH": ("p", "q")}

# Поправка 1: класс в объявлении базы («∀ G конечная», «∀ G абелева») — посылка класса
# на главную переменную не считается. ALGEN_CLASS=finite: перебор по строкам, где
# первая групповая переменная базы конечна, с этой посылкой как посылкой записи.
CLASS = os.environ.get("ALGEN_CLASS", "")


def _swap(s, pair):
    import re
    a, b = pair
    return re.sub(rf"\b({a}|{b})\b", lambda m: b if m.group(1) == a else a, s)


def schemes(vocab, base, k=2, t=None):
    """Схемы базы: (id, термы-строки) — замыкания наборов из ⩽ t верхних термов
    вселенной (по умолчанию t = k + 1), без повторов. id — номера термов вселенной через «-»."""
    t = k + 1 if t is None else t
    g, _, _ = scheme(vocab, {"раздел": "grp", "условие": BASES[base]})
    names = {str(t): t for t in g.terms}
    uni = universe(vocab, base)
    ts = [term(g, x, names, "grp") for x in uni]
    num = {t: i + 1 for i, t in enumerate(ts)}
    # термы самой записи базы (A ∗ B в «H : Sub(A ∗ B)») входят во все схемы; номер — после вселенной
    for x in g.terms:
        if isinstance(x, App) and x not in num:
            num[x] = len(num) + 1
    vars_ = [t for t in g.terms if isinstance(t, Var)]
    seen, out = set(), []
    swap = SWAP.get(base)
    for r in range(0, (SIZE if SIZE else t) + 1):
        for pick in combinations(ts, r):
            if SIZE:
                if len(set().union(*(app_nodes(x) for x in pick))) > SIZE if pick else False:
                    continue
                # набор, где один терм — подтерм другого, даёт ту же схему, что больший терм
                if any(x in subterms(y) for x in pick for y in pick if x != y):
                    continue
            cl = closure(g, list(pick) + vars_)
            if not SIZE and len(maximal(g, cl)) > t:
                continue
            terms_ = sorted((t for t in cl if isinstance(t, App)), key=lambda x: (num.get(x, 10 ** 6), str(x)))
            key = tuple(terms_)
            if key in seen:
                continue
            seen.add(key)
            if swap:
                # схема, симметричная уже взятой (A ↔ B, H ↔ K), — тот же набор задач
                try:
                    tw = tuple(sorted({term(g, _swap(str(t), swap), names, "grp") for t in terms_}, key=num.get))
                except Exception:
                    tw = None
                if tw is not None and tw != key and tw in seen:
                    continue
                if tw is not None:
                    seen.add(tw)
            sid = base + ("-" + "-".join(str(num[t]) for t in terms_) if terms_ else "")
            out.append((sid, [str(t) for t in terms_]))
    return out


# --- таблица ------------------------------------------------------------------

def grow_ops(vocab):
    """Достраивать служебные конструкции и дешёвые унарные (Z, ′, кручение),
    но не конструкции вселенной: их термы уже даны."""
    return set(vocab.cons) - set(CONS) - NO_GROW | {"center", "commutator", "torsion"}


# Семейства C(n), S(n), A(n), D(n) и n!, n + n не достраиваются: правила о них
# (партия 18) со сценой «∀ n : Num» иначе строят их от каждого числового терма
# базы (у G — 113 чисел, ≈ 900 новых термов, каркас — больше 9 ГБ вместо 0,7).
# Правила применяются к членам семейств, которые уже есть во вселенной.
NO_GROW = {"cyc", "sym-n", "alt", "dih", "num-fact", "num-add"}


def skeleton(lib, vocab, base, part=None, with_rows=False):
    return E.SchemeForm(lib, vocab, BASES[base], universe(vocab, base),
                        grow_ops=grow_ops(vocab), part=part, with_rows=with_rows)


def _fp(base):
    mode = (f":s{SIZE}" if SIZE else "") + (":быстро" if E.FAST_DERIVE else "")
    return f"{_fingerprint()}:{base}:{','.join(sorted(E.SKIP))}{mode}"


def theory_fp(base, form=None):
    """Хэш того, от чего зависит вывод строки по её записанным значениям.

    С каркасом базы (form) хэш смысловой: клаузы теории, нумерация её атомов,
    атомы таблицы и код `_derive`. Правки остального кода (перебор, сводка)
    кэш не сбрасывают, а любая правка правил или словаря — сбрасывает.
    Без каркаса — по файлам, как раньше."""
    import hashlib
    import inspect
    h = hashlib.sha256()
    if form is not None:
        T = form.sc.T
        h.update(repr([str(a) for a in T.atoms]).encode())
        for c in sorted(tuple(sorted(c)) for c in T.clauses):  # порядок заземления не важен
            h.update(repr(c).encode())
        h.update(repr([str(a) for a in form.atoms]).encode())
        h.update(inspect.getsource(E.SchemeForm._derive).encode())
        h.update(f"{E.DIVERSE}:{E.REFRESH}".encode())
        h.update(f"{base}:{','.join(sorted(E.SKIP))}".encode())
        return "т" + h.hexdigest()[:15]
    root = Path(__file__).resolve().parents[2]
    files = [root / "data" / "grp.json", root / "data" / "new" / "grp.json", root / "data" / "vocab" / "grp.json",
             *(Path(__file__).parent / f for f in ("logic.py", "enumerate.py", "library.py", "table.py", "etalon.py"))]
    for f in files:
        if f.exists():
            h.update(f.name.encode())
            h.update(f.read_bytes())
    h.update(f"{base}:{','.join(sorted(E.SKIP))}".encode())
    return h.hexdigest()[:16]


def _pack_rows(d):
    """{ключ: [True/False/None, …]} → {ключ: (биты «верно», биты «ложно»)}."""
    out = {}
    for k, row in d.items():
        t = np.packbits(np.array([v is True for v in row], dtype=bool))
        f = np.packbits(np.array([v is False for v in row], dtype=bool))
        out[k] = (t.tobytes(), f.tobytes(), len(row))
    return out


def _unpack_rows(d):
    out = {}
    for k, (t, f, n) in d.items():
        tt = np.unpackbits(np.frombuffer(t, dtype=np.uint8))[:n]
        ff = np.unpackbits(np.frombuffer(f, dtype=np.uint8))[:n]
        out[k] = [True if a else (False if b else None) for a, b in zip(tt, ff)]
    return out


def load_cache(base, cdir, form=None):
    """Выводы строк базы из кэша прошлых прогонов (только с тем же theory_fp)."""
    if not cdir or not Path(cdir).exists():
        return {}
    fp, rows = theory_fp(base, form), {}
    for path in Path(cdir).rglob(f"{base}.*.dcache"):
        try:
            with open(path, "rb") as fh:
                data = pickle.load(fh)
        except Exception:
            continue
        if data.get("отпечаток") == fp:
            rows.update(data["строки"])
    return _unpack_rows(rows)


def rules_fp(vocab):
    """Отпечатки правил и вырождений словаря (по содержанию): кэш подсказок (A4)
    годится, если все правила прошлого прогона есть и сейчас."""
    import hashlib
    out = set()
    for r in list(vocab.rules) + list(vocab.degen):
        out.add(hashlib.sha1(json.dumps(r, sort_keys=True, ensure_ascii=False, default=str).encode()).hexdigest()[:16])
    return out


def load_hints(base, cdir, form):
    """Подсказки для _derive из *.hcache прошлых прогонов (A4): выведенные значения
    по именам атомов, если правила того прогона — подмножество нынешних.
    Атомы, которых нет в нынешней таблице, пропускаются; новых атомов в
    подсказке нет — их ядро ищется заново."""
    if not cdir or not Path(cdir).exists():
        return {}
    now = rules_fp(form.g.v)
    by_name = {E.atom_name(a): a for a in form.atoms}
    hints, used, skipped = {}, 0, 0
    for path in Path(cdir).rglob(f"{base}.*.hcache"):
        try:
            with open(path, "rb") as fh:
                data = pickle.load(fh)
        except Exception:
            continue
        if not data["правила"] <= now:
            skipped += 1
            continue
        used += 1
        atoms = [by_name.get(n) for n in data["атомы"]]
        for k, row in _unpack_rows(data["строки"]).items():
            hints[k] = {a: v for a, v in zip(atoms, row) if a is not None and v is not None}
    print(f"{base}: подсказок {len(hints)} из {used} файлов кэша (пропущено {skipped}: правила сняты или изменены)",
          file=sys.stderr)
    return hints


def build(lib, vocab, base, part, outdir, skel=None):
    """Часть таблицы базы. skel — готовый каркас (теория строится один раз на
    базу, части получают его через fork); иначе строится здесь."""
    t0 = time.time()
    if skel is not None:
        f = skel
        f.sc.s = f.sc.T.solver()  # свой решатель в дочернем процессе
        f.fill_rows(part)
    else:
        f = skeleton(lib, vocab, base, part=part, with_rows=True)
    path = Path(outdir) / f"{base}.{part[0]}-{part[1]}.pickle"
    path.parent.mkdir(parents=True, exist_ok=True)
    data = {"отпечаток": _fp(base), "атомов": len(f.atoms), "envs": f.envs, "skipped": f.skipped,
            **{k: np.packbits(getattr(f, k), axis=1) for k in "mse"}}
    tmp = path.with_suffix(".tmp")  # атомарно: задание, убитое по времени, не оставит обрывка
    with open(tmp, "wb") as fh:
        pickle.dump(data, fh, protocol=pickle.HIGHEST_PROTOCOL)
    # кэш выводов этой части (ключ — записанные значения строки) для следующих прогонов
    used = {k: f._derived[k] for k in getattr(f, "_used", ()) if k in f._derived}
    new = [k for k in used if k not in getattr(f, "_cached_keys", ())]
    dpath = Path(outdir) / f"{base}.{part[0]}-{part[1]}.dcache"
    with open(dpath.with_suffix(".dtmp"), "wb") as fh:
        pickle.dump({"отпечаток": theory_fp(base, f), "строки": _pack_rows(used)}, fh, protocol=pickle.HIGHEST_PROTOCOL)
    os.replace(dpath.with_suffix(".dtmp"), dpath)
    # A4: те же выводы по именам атомов — годятся прогонам с надмножеством правил
    nk = getattr(f, "_nk", {})
    rows2 = {nk[k]: v for k, v in used.items() if k in nk}
    hpath = Path(outdir) / f"{base}.{part[0]}-{part[1]}.hcache"
    with open(hpath.with_suffix(".htmp"), "wb") as fh:
        pickle.dump({"правила": rules_fp(f.g.v), "атомы": [E.atom_name(a) for a in f.atoms],
                     "строки": _pack_rows(rows2)}, fh, protocol=pickle.HIGHEST_PROTOCOL)
    os.replace(hpath.with_suffix(".htmp"), hpath)
    os.replace(tmp, path)  # часть готова, когда есть её .pickle
    print(f"{base} {part[0]}/{part[1]}: строк {len(f.envs)}, атомов {len(f.atoms)}, новых выводов {len(new)}, "
          f"{round(time.time() - t0)} с → {path}", file=sys.stderr)


# Частей таблицы на базу (по числу строк и цене строки).
# COST — ядро-часы на базу: замер 1.11 (проба ~30 строк, × 3 — поправка по
# полной таблице G: проба дала 0,9, вышло 2,7). Части по ~1,5 ядро-часа:
# задание GitHub длится не больше 6 часов, готовые части выгружаются, а
# повторный запуск (PREV_BUILD) досчитывает недостающие.
# Часов на одну нить (замер 2.11: доля таблицы локально × 1,25 — машины GitHub медленнее)
COST = {"G": 13.0, "GN": 145.0, "AB": 43.0, "GHK": 230.0, "GMN": 44.0, "GHF": 61.0, "Fam": 0.01,
        "GX": 0.3, "Gx": 2.0, "GE": 7.0, "GXxy": 2.0, "Gxy": 0.5, "D": 0.01, "MN": 0.01, "ABH": 0.1,
        "ABC": 0.5, "n": 0.01, "pG": 0.05, "pqG": 0.4, "pGH": 0.3, "pqGH": 1.4}
PARTS = {b: max(1, round(c / 1.5)) for b, c in COST.items()}


def assignment(jobs):
    """Части таблиц по машинам: самые дорогие — первыми, каждая — на наименее
    загруженную машину (одинаково на всех машинах: порядок детерминирован)."""
    tasks = [(b, (i, n)) for b, n in PARTS.items() for i in range(1, n + 1)]
    tasks.sort(key=lambda t: (-COST[t[0]] / PARTS[t[0]], t[0], t[1]))
    load = [0.0] * jobs
    out = [[] for _ in range(jobs)]
    for b, part in tasks:
        j = min(range(jobs), key=lambda x: (load[x], x))
        load[j] += COST[b] / PARTS[b]
        out[j].append((b, part))
    for o in out:  # одна база подряд: каркас строится один раз
        o.sort(key=lambda t: (list(PARTS).index(t[0]), t[1]))
    return out


def build_all(lib, vocab, job, jobs, outdir, threads, cache=None):
    """Задание job из jobs: части таблиц job, job + jobs, … по threads процессов."""
    # дешёвые базы первыми: их таблицы будут готовы, даже если задание не уложится по времени
    mine = sorted(assignment(jobs)[job - 1], key=lambda t: (COST[t[0]], t[0], t[1]))
    ctx = mp.get_context("fork")
    running = []
    skel = {}
    for b, part in mine:
        done = Path(outdir) / f"{b}.{part[0]}-{part[1]}.pickle"
        if done.exists():
            try:
                with open(done, "rb") as fh:
                    if pickle.load(fh)["отпечаток"] == _fp(b):
                        print(f"{b} {part[0]}/{part[1]}: уже есть", file=sys.stderr, flush=True)
                        continue
            except Exception:
                pass
        while True:
            running = [p for p in running if p.exitcode is None]
            if len(running) < threads:
                break
            time.sleep(0.5)
        if b not in skel:  # каркас базы — один раз на машину; прошлый не держим (части — копии через fork)
            skel.clear()
            import gc
            gc.collect()
            t = time.time()
            skel[b] = skeleton(lib, vocab, b)
            cached = load_cache(b, cache, skel[b])
            skel[b]._derived.update(cached)
            skel[b]._cached_keys = set(cached)
            skel[b]._hints = load_hints(b, cache, skel[b])
            print(f"{b}: каркас {round(time.time() - t)} с, из кэша выводов {len(cached)}", file=sys.stderr, flush=True)
        p = ctx.Process(target=build, args=(lib, vocab, b, part, outdir, skel[b]))
        p.start()
        running.append(p)
    for p in running:
        p.join()


def load(lib, vocab, base, tdir):
    """Каркас базы со строками из всех частей таблицы."""
    parts = sorted(Path(tdir).glob(f"{base}.*-*.pickle"))
    if not parts:  # до каркаса: каркас G — минуты, а таблицы может и не быть
        raise FileNotFoundError(f"нет таблицы {base} в {tdir}")
    f = skeleton(lib, vocab, base)
    n = int(parts[0].stem.split("-")[-1])
    if len(parts) != n:
        raise FileNotFoundError(f"{base}: частей {len(parts)} из {n}")
    mats = {k: [] for k in "mse"}
    f.envs, f.skipped = [], []
    width = 2 * len(f.atoms)
    for p in parts:
        with open(p, "rb") as fh:
            d = pickle.load(fh)
        if d["атомов"] != len(f.atoms):
            raise ValueError(f"{p}: таблица от другого словаря (атомов {d['атомов']}, а не {len(f.atoms)})")
        if d["отпечаток"] != _fp(base):
            # ALGEN_STALE=1: таблица прошлых правил. Верно, если с тех пор правила только
            # добавлялись, а данные библиотеки не правились: выведенные значения строк
            # остаются выводами, просто часть новых не выведена. Иначе — ошибка.
            if not os.environ.get("ALGEN_STALE"):
                raise ValueError(f"{p}: таблица от другого кода или данных")
            print(f"{p}: таблица прошлых правил (ALGEN_STALE)", file=sys.stderr)
        f.envs += d["envs"]
        f.skipped += d["skipped"]
        for k in "mse":
            mats[k].append(d[k])  # упакованные биты: в 8 раз меньше, распаковка — ниже, на место
        del d
    rows = sum(x.shape[0] for x in mats["m"])
    for k in "mse":  # без промежуточных копий: у G при s ⩽ 2 одна матрица — больше 1 ГБ
        out = np.empty((rows, width), dtype=bool)
        r = 0
        for x in mats[k]:
            out[r:r + x.shape[0]] = np.unpackbits(x, axis=1, count=width).view(bool)
            r += x.shape[0]
        mats[k] = None
        setattr(f, k, out)
    f.names = list(range(len(f.envs)))
    return f


def save_reps(f, base, tdir):
    with open(Path(tdir) / f"{base}.rep.pickle", "wb") as fh:
        pickle.dump({"отпечаток": _fp(base), "атомов": len(f.atoms), "rep": f.rep, "rep_flat": f.rep_flat}, fh)


def load_reps(f, base, tdir):
    """Готовые классы равносильных (команда «равносильные»): у G их счёт — около 2 ч."""
    p = Path(tdir) / f"{base}.rep.pickle"
    if not p.exists():
        return False
    with open(p, "rb") as fh:
        d = pickle.load(fh)
    if d["отпечаток"] != _fp(base) or d["атомов"] != len(f.atoms):
        print(f"{p}: классы от другой таблицы, считаю заново", file=sys.stderr)
        return False
    f.rep, f.rep_flat = d["rep"], d["rep_flat"]
    return True


def equiv_reps(f):
    """Классы равносильных литералов базы: rep[j] — представитель класса столбца j.

    Кандидаты — литералы с одинаковыми столбцами строк (литерал и отрицание);
    равносильность проверяется теорией базы в обе стороны (при посылках записи).
    Представитель — литерал с наименьшим числом построенных термов, затем короче.
    Набор с литералом и набор с его представителем — один факт: перебирать
    достаточно представителей."""
    from collections import defaultdict
    from .logic import decide
    n = f.m.shape[1]
    name = lambda j: ("¬" if j % 2 else "") + E.atom_name(f.atoms[j // 2])

    def napps(j):
        out = set()
        for x in f.atoms[j // 2][2:]:
            if isinstance(x, App):
                out |= {y for y in subterms(x) if isinstance(y, App)}
        return len(out)

    buckets = defaultdict(list)
    for j in range(n):
        buckets[(f.m[:, j].tobytes(), f.m[:, j ^ 1].tobytes())].append(j)
    fixed = [f.lit(j) for j in f.fixed]
    rep = list(range(n))
    for js in buckets.values():
        if len(js) < 2:
            continue
        js = sorted(js, key=lambda j: (napps(j), len(name(j)), j))
        classes = []  # внутри корзины: несколько классов с одинаковыми столбцами
        for j in js:
            for c in classes:
                r = c[0]
                if decide(f.sc.T, fixed + [f.lit(r)], f.lit(j), f.sc.s).kind == "выводится" and \
                        decide(f.sc.T, fixed + [f.lit(j)], f.lit(r), f.sc.s).kind == "выводится":
                    c.append(j)
                    rep[j] = r
                    break
            else:
                classes.append([j])
    f.rep = rep
    f.rep_flat = {j for j in range(n) if napps(j) == 0}
    return rep


def drop_equiv(f, cols=None):
    """Столбцы формы, которые не перебираются: у литерала есть равносильный
    представитель в этой же форме или без построенных термов (он есть в каждой).
    Литералы-требования других атомов (abelian(G) для ulm(G)) не отбрасываются."""
    b = getattr(f, "_base", f)
    rep = getattr(b, "rep", None)
    if rep is None:
        return set()
    cols = list(range(len(rep))) if cols is None else [int(c) for c in cols]
    where = {c: i for i, c in enumerate(cols)}
    needed = set()
    for r in (f.req or {}).values():
        needed |= set(r) | {x ^ 1 for x in r}
    needed |= set(f.fixed) | {x ^ 1 for x in f.fixed}
    out = set()
    for i, c in enumerate(cols):
        r = rep[c]
        if r != c and i not in needed and (r in where or r in b.rep_flat):
            out.add(i)
    return out


def view(base_form, terms):
    """Схема-вид: столбцы таблицы для переменных базы и термов terms."""
    b = base_form
    g = b.g
    by_name = {str(t): t for t in b.own}
    elems = {t for t in b.own if isinstance(t, Var)} | {by_name[x] for x in terms}
    v = object.__new__(E.SchemeForm)
    v.g, v.lib, v.sc, v.search = g, b.lib, b.sc, b.search
    v._kept, v._derived, v._facts = {}, {}, b._facts
    v.envs, v.skipped, v.names = b.envs, b.skipped, b.names
    v.fixed_lits = b.fixed_lits
    v.own = [t for t in b.own if t in elems]
    v.atoms = [a for a in b.atoms if all(x in elems for x in a[2:] if not isinstance(x, (str, int)))]
    v.index = {a: i for i, a in enumerate(v.atoms)}
    v.req = {}
    for i, a in enumerate(v.atoms):
        need = {2 * v.index[("p", p, u)] for t in a[2:] if not isinstance(t, (str, int)) for p, u in g.requires(t) if ("p", p, u) in v.index}
        if need:
            v.req[i] = need
    v.fixed = [2 * v.index[a] + (0 if val else 1) for a, val in b.fixed_lits if a in v.index]
    if CLASS:
        X = next((t for t in v.own if isinstance(t, Var) and g.terms[t].sort == "Grp.obj"), None)
        a = ("p", CLASS, X)
        if X is not None and a in v.index:
            v.fixed_lits = list(v.fixed_lits) + [(a, True)]
            v.fixed = v.fixed + [2 * v.index[a]]
    cols = np.array([2 * b.index[a] + d for a in v.atoms for d in (0, 1)], dtype=np.int64)
    v.m, v.s, v.e = b.m[:, cols], b.s[:, cols], b.e[:, cols]
    v._base, v._base_cols = b, cols
    v.drop = drop_equiv(v, cols)
    top = maximal(g, elems)
    v.need = [{i for i, a in enumerate(v.atoms) if t in a[2:]} for t in top]
    sw = SWAP.get(_STATE.get("base_of", {}).get(id(b)))
    if sw:  # парные атомы «P(A) и P(B)» для симметричных переменных базы
        vs = {str(t): t for t in v.own if isinstance(t, Var)}
        if sw[0] in vs and sw[1] in vs:
            v.pairs = [(vs[sw[0]], vs[sw[1]])]
    gb = _STATE.get("forms", {}).get("G") or _STATE.get("generic")
    if gb is not None:
        GV = next(t for t in gb.own if isinstance(t, Var))
        v.generic = (gb.m if E.CLOSE_MARKED else gb.e, {a[1]: i for i, a in enumerate(gb.atoms) if a[0] == "p" and a[2] == GV})
    return v


# --- перебор схем из таблиц ---------------------------------------------------

_STATE = {}


def k_for(ks, n_top):
    """Посылок для схемы с n_top верхними термами: ks = [k при 0 термов, при 1, …];
    последнее значение — для всех больших."""
    return ks[min(n_top, len(ks) - 1)]


class SchemeTimeout(Exception):
    pass


def _alarm(signum, frame):
    raise SchemeTimeout()


def _one(job):
    base, sid, terms, k, outdir, fp = job
    out, err = io.StringIO(), io.StringIO()
    t0 = time.time()
    limit = _STATE.get("limit") or 0
    if limit:
        signal.signal(signal.SIGALRM, _alarm)
        signal.alarm(int(limit))
    try:
        form = view(_STATE["forms"][base], terms)
        form, alive, empty, report = E.run(k, _STATE["lib"], _STATE["vocab"], form)
        summary = E.render(form, alive, empty, report, out=out, err=err, registry=_STATE["registry"])
        status = "ok"
    except SchemeTimeout:
        summary, status = {}, f"таймаут {limit} с"
    except Exception:
        summary, status = {}, "ошибка"
        err.write(traceback.format_exc())
    finally:
        if limit:
            signal.alarm(0)
    rec = {"id": sid, "условие": BASES[base] + (f"; класс {CLASS}" if CLASS else ""), "термы": terms, "посылок": k, "без": sorted(E.SKIP),
           "отпечаток": fp, "секунд": round(time.time() - t0, 1), "статус": status, **summary}
    p = Path(outdir) / sid
    p.with_suffix(".txt").write_text(err.getvalue() + "\n" + out.getvalue(), encoding="utf-8")
    p.with_suffix(".json").write_text(json.dumps(rec, ensure_ascii=False, indent=1), encoding="utf-8")


def run_schemes(a):
    """Перебор схем по таблицам баз. Базы — по одной: таблица базы загружается,
    её схемы перебираются, таблица выгружается (в памяти машины — одна база,
    а не все сразу: иначе 16 ГБ машины GitHub не хватало)."""
    import gc
    vocab = Vocab.section("grp")
    lib = built_library(vocab)
    E.DEFER = getattr(a, "defer", 0) or 0
    from . import fast
    fast.install()  # вывод через банк моделей теории (ответы те же, что у logic.decide)
    _STATE.update(lib=lib, vocab=vocab, registry=E.load_registry(), forms={})
    outdir = Path(a.out)
    outdir.mkdir(parents=True, exist_ok=True)
    ks = [int(x) for x in str(a.k).split(",")]
    try:  # таблица базы G — для фильтра условий об одном терме (generic_filter)
        _STATE["generic"] = load(lib, vocab, "G", a.dir)
    except (FileNotFoundError, ValueError) as e:
        print(f"нет таблицы G для фильтра: {e}", file=sys.stderr)
    by_base = {}
    for base in a.bases.split(","):
        fp = _fp(base) + f":{a.k}" + (f":d{a.defer}" if a.defer else "")
        todo = schemes(vocab, base, ks[-1], getattr(a, "t", None))
        g0, _, _ = scheme(vocab, {"раздел": "grp", "условие": BASES[base]})
        n0 = {str(t): t for t in g0.terms}
        tops = {}
        for sid, terms in todo:
            ts = [term(g0, x, n0, "grp") for x in terms]
            tops[sid] = sum(1 for t in maximal(g0, closure(g0, ts + [t for t in g0.terms if isinstance(t, Var)]))
                            if isinstance(t, App))
        if getattr(a, "sample", 1) > 1:  # каждая N-я схема базы: круг библиотеки по всем базам сразу
            todo = todo[::a.sample]
        if a.part:
            i, n = map(int, a.part.split("/"))
            todo = todo[i - 1::n]
        jobs = []
        for sid, terms in todo:
            j = outdir / f"{sid}.json"
            if j.exists() and not a.force:
                try:
                    old = json.loads(j.read_text(encoding="utf-8"))
                    if old.get("отпечаток") == fp and old.get("статус") == "ok":
                        continue
                except Exception:
                    pass
            jobs.append((base, sid, terms, k_for(ks, tops[sid]), str(outdir), fp))
        if jobs:
            by_base[base] = jobs
    total = sum(len(j) for j in by_base.values())
    print(f"схем к перебору {total}, нитей {a.jobs}: " + ", ".join(f"{b} {len(j)}" for b, j in by_base.items()),
          file=sys.stderr, flush=True)
    t0 = time.time()
    _STATE["limit"] = a.limit
    deadline = t0 + a.until * 60 if a.until else None
    _STATE["deadline"] = deadline  # видят и дочерние процессы (fork)
    done = 0
    for base, jobs in by_base.items():
        if deadline and time.time() > deadline:
            print(f"срок вышел: база {base} не начата ({len(jobs)} схем)", file=sys.stderr, flush=True)
            continue
        t = time.time()
        if base == "G" and _STATE.get("generic") is not None:
            _STATE["forms"][base] = _STATE["generic"]
        else:
            _STATE["forms"][base] = load(lib, vocab, base, a.dir)
        _STATE.setdefault("base_of", {})[id(_STATE["forms"][base])] = base
        if not getattr(a, "no_equiv", False) and getattr(_STATE["forms"][base], "rep", None) is None:
            if not load_reps(_STATE["forms"][base], base, a.dir):
                equiv_reps(_STATE["forms"][base])
        print(f"{base}: таблица {_STATE['forms'][base].e.shape}, {round(time.time() - t)} с",
              file=sys.stderr, flush=True)
        done = _run_pool(jobs, a, deadline, t0, done, total)
        if base != "G":
            del _STATE["forms"][base]
        gc.collect()
    print(f"готово за {round(time.time() - t0)} с", file=sys.stderr)


def _run_pool(jobs, a, deadline, t0, done, total):
    """Схемы jobs по a.jobs процессам (fork от родителя с загруженной таблицей)."""
    ctx = mp.get_context("fork")  # таблицы наследуются без копирования
    limit = int(a.mem * 2**30) if a.mem else 0

    def worker(chunk):
        if limit:
            # предел — сверх уже занятого: таблицы баз унаследованы от родителя (fork)
            # и входят в адресное пространство, хотя памяти не занимают повторно
            import resource
            vm = 0
            with open("/proc/self/status") as fh:
                for line in fh:
                    if line.startswith("VmSize:"):
                        vm = int(line.split()[1]) * 1024
            resource.setrlimit(resource.RLIMIT_AS, (vm + limit, vm + limit))
        for job in chunk:
            if _STATE.get("deadline") and time.time() > _STATE["deadline"]:
                break  # срок вышел: схемы пачки после него не начинаем
            try:
                _one(job)
            except MemoryError:
                p = Path(job[4]) / job[1]
                p.with_suffix(".json").write_text(json.dumps(
                    {"id": job[1], "условие": BASES[job[0]], "термы": job[2], "отпечаток": job[5],
                     "статус": "ошибка: память"}, ensure_ascii=False), encoding="utf-8")
        os._exit(0)

    # Дочерний процесс берёт пачку схем (форк на каждую схему дорог при тысячах схем).
    size = max(1, min(20, len(jobs) // (a.jobs * 4) or 1))
    queue = [jobs[i:i + size] for i in range(0, len(jobs), size)]
    running = {}
    while queue or running:
        if deadline and time.time() > deadline and queue:
            print(f"срок вышел: не начато схем {sum(len(c) for c in queue)}", file=sys.stderr, flush=True)
            queue = []
        while queue and len(running) < a.jobs:
            chunk = queue.pop(0)
            p = ctx.Process(target=worker, args=(chunk,))
            p.start()
            running[p] = chunk
        for p in list(running):
            if p.exitcode is None:
                continue
            chunk = running.pop(p)
            done += len(chunk)
            if p.exitcode != 0:
                for job in chunk:
                    j = Path(job[4]) / f"{job[1]}.json"
                    if not j.exists():
                        j.write_text(json.dumps({"id": job[1], "условие": BASES[job[0]], "термы": job[2],
                                                 "отпечаток": job[5], "статус": f"ошибка: код {p.exitcode}"},
                                                ensure_ascii=False), encoding="utf-8")
            print(f"[{done}/{total}] {round(time.time() - t0)} с", file=sys.stderr, flush=True)
        time.sleep(0.2)
    return done


def completeness(lib, vocab, base, tdir, top=15):
    """Полнота библиотеки по термам вселенной: доля известных значений атомов
    терма по строкам, где терм существует, и группы с наибольшим числом
    неизвестных значений (что вписать в библиотеку в первую очередь)."""
    from collections import Counter
    f = load(lib, vocab, base, tdir)
    known = f.e[:, 0::2] | f.e[:, 1::2]
    out = []
    for t in f.own:
        idx = [i for i, a in enumerate(f.atoms) if a[0] == "p" and a[2] == t]
        if not idx:
            continue
        rows = np.array([f.search._image(t, env) is not None or isinstance(t, Var) for env in f.envs])
        k = known[:, idx]
        miss = Counter()
        for r in np.flatnonzero((~k).any(axis=1)):
            env = f.envs[r]
            g = next(iter(env.values()))
            miss[lib.obj[g[1]].get("имя", g[1])] += int((~k[r]).sum())
        out.append((str(t), float(k.mean()), float(rows.mean()), miss.most_common(top)))
    return out


def k1_base(a):
    """Остаток k = 1 по всей базе (одна задача на базу, без схем): запреты из двух
    литералов, которые не выводятся и не опровергаются, с вопросами «какие группы
    бывают с S». Пишет k1-<база>.json и k1-<база>-вопросы.txt в a.out."""
    from collections import Counter
    from . import fast
    vocab = Vocab.section("grp")
    lib = built_library(vocab)
    fast.install()
    E.DEFER = 0.15
    t = time.time()
    f = load(lib, vocab, a.base, a.dir)
    gen = f if a.base == "G" else load(lib, vocab, "G", a.dir)
    _STATE.update(forms={a.base: f}, generic=gen, base_of={id(f): a.base})
    if not getattr(a, "no_equiv", False):
        equiv_reps(f)
        f.drop = drop_equiv(f)
        print(f"{a.base}: равносильных литералов не перебирается {len(f.drop)} из {f.m.shape[1]}", file=sys.stderr)
    form, alive, empty, rep = E.run(1, lib, vocab, f)
    res = {}
    for r in rep:
        if r["вердикт"] == "неизвестно":  # компактно: у больших баз остаток — сотни тысяч запретов
            q = r.get("вопрос")
            res.setdefault(tuple(r["запрет"]), {"запрет": r["запрет"], "цель": r["цель"], "вопрос": q,
                                                 "значения": r.get("значения", [])[:3]})
    groups = {}
    for r in res.values():
        q = r.get("вопрос")
        if q:
            groups.setdefault(q["S"], [0, q])[0] += 1
    out = Path(a.out)
    out.mkdir(parents=True, exist_ok=True)
    summary = {"база": a.base, "секунд": round(time.time() - t), "строк": len(f.envs), "атомов": len(f.atoms),
               "пропущено строк": len(f.skipped), "вердикты": dict(Counter(r["вердикт"] for r in rep)),
               "запретов": len(res), "с вопросом": sum(1 for r in res.values() if r.get("вопрос")),
               "вопросов": len(groups)}
    with open(out / f"k1-{a.base}.json", "w") as fh:
        json.dump({"сводка": summary, "пропущено": f.skipped[:200], "остаток": list(res.values())},
                  fh, ensure_ascii=False, default=lambda x: x.item() if hasattr(x, "item") else str(x))
    with open(out / f"k1-{a.base}-вопросы.txt", "w") as fh:
        for S, (c, q) in sorted(groups.items(), key=lambda x: -x[1][0]):
            fh.write(f"{c}\t{q['групп']}\t{q.get('неизвестно')}\t{S}\t{'; '.join(q['группы'])}\n")
    print(json.dumps(summary, ensure_ascii=False), file=sys.stderr)


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    sub = ap.add_subparsers(dest="cmd", required=True)
    for name in ("вселенная", "схемы"):
        s = sub.add_parser(name)
        s.add_argument("base")
        s.add_argument("--посылок", dest="k", type=int, default=2)
        s.add_argument("--термов", dest="t", type=int, default=None, help="верхних термов в схеме (по умолчанию k + 1)")
    s = sub.add_parser("строить")
    s.add_argument("base")
    s.add_argument("--часть", dest="part", default="1/1")
    s.add_argument("--каталог", dest="dir", required=True)
    s.add_argument("--без", dest="skip", default="")
    s.add_argument("--кэш", dest="cache", default=None, help="каталог с *.dcache / *.hcache прошлых прогонов")
    s = sub.add_parser("строить-все")
    s.add_argument("--задание", dest="job", required=True, help="j/N")
    s.add_argument("--каталог", dest="dir", required=True)
    s.add_argument("--нитей", dest="jobs", type=int, default=mp.cpu_count())
    s.add_argument("--без", dest="skip", default="")
    s.add_argument("--кэш", dest="cache", default=None, help="каталог с *.dcache прошлых прогонов")
    s = sub.add_parser("k1", help="остаток k = 1 по всей базе")
    s.add_argument("base")
    s.add_argument("--каталог", dest="dir", required=True)
    s.add_argument("--выход", dest="out", required=True)
    s.add_argument("--без", dest="skip", default="")
    s = sub.add_parser("равносильные", help="классы равносильных литералов базы — один раз, в файл <база>.rep.pickle")
    s.add_argument("base")
    s.add_argument("--каталог", dest="dir", required=True)
    s.add_argument("--без", dest="skip", default="")
    s = sub.add_parser("полнота")
    s.add_argument("base")
    s.add_argument("--каталог", dest="dir", required=True)
    s.add_argument("--без", dest="skip", default="")
    s = sub.add_parser("перебор")
    s.add_argument("bases", help="базы через запятую")
    s.add_argument("--каталог", dest="dir", required=True, help="где таблицы")
    s.add_argument("--выход", dest="out", required=True)
    s.add_argument("--часть", dest="part")
    s.add_argument("--нитей", dest="jobs", type=int, default=mp.cpu_count())
    s.add_argument("--посылок", dest="k", default="2",
                   help="k или список «k0,k1,k2»: посылок для схем с 0, 1, ⩾ 2 верхними термами")
    s.add_argument("--без", dest="skip", default="")
    s.add_argument("--заново", dest="force", action="store_true")
    s.add_argument("--память", dest="mem", type=float, default=0)
    s.add_argument("--отложить", dest="defer", type=float, default=0,
                   help="откладывать атомы, известные меньше чем в этой доле строк (например 0.15)")
    s.add_argument("--до", dest="until", type=float, default=0, help="минут: после этого новые схемы не начинать")
    s.add_argument("--предел", dest="limit", type=float, default=0, help="секунд на одну схему")
    s.add_argument("--выборка", dest="sample", type=int, default=1, help="брать каждую N-ю схему базы")
    s.add_argument("--термов", dest="t", type=int, default=None, help="верхних термов в схеме (по умолчанию k + 1)")
    a = ap.parse_args()
    E.SKIP.update(x.strip() for x in getattr(a, "skip", "").split(",") if x.strip())
    vocab = Vocab.section("grp")
    if a.cmd == "вселенная":
        for i, x in enumerate(universe(vocab, a.base)):
            print(i + 1, x)
    elif a.cmd == "схемы":
        ss = schemes(vocab, a.base, a.k, a.t)
        for sid, ts in ss:
            print(f"{sid} | {BASES[a.base]} | {'; '.join(ts)}")
        print(f"# схем {len(ss)}", file=sys.stderr)
    elif a.cmd == "строить":
        i, n = map(int, a.part.split("/"))
        lib = built_library(vocab)
        skel = None
        if a.cache:
            skel = skeleton(lib, vocab, a.base)
            cached = load_cache(a.base, a.cache, skel)
            skel._derived.update(cached)
            skel._cached_keys = set(cached)
            skel._hints = load_hints(a.base, a.cache, skel)
        build(lib, vocab, a.base, (i, n), a.dir, skel)
    elif a.cmd == "полнота":
        for t, k, im, miss in completeness(built_library(vocab), vocab, a.base, a.dir):
            print(f"{t:36s} известно {k:.0%}, образ в библиотеке {im:.0%}")
            print("    больше всего неизвестных: " + "; ".join(f"{g} {n}" for g, n in miss[:8]))
    elif a.cmd == "k1":
        k1_base(a)
    elif a.cmd == "равносильные":
        t = time.time()
        f = load(built_library(vocab), vocab, a.base, a.dir)
        equiv_reps(f)
        save_reps(f, a.base, a.dir)
        print(f"{a.base}: классы равносильных за {round(time.time() - t)} с", file=sys.stderr)
    elif a.cmd == "строить-все":
        j, n = map(int, a.job.split("/"))
        build_all(built_library(vocab), vocab, j, n, a.dir, a.jobs, a.cache)
    else:
        run_schemes(a)


if __name__ == "__main__":
    main()
