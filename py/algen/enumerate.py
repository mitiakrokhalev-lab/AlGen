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
from itertools import combinations

import numpy as np

from .library import GROUP_PROPS, MARKS, SUB_PROPS, Library, Scene, jobs
from .logic import Vocab, decide


def atom_name(a):
    return f"{a[1]}({', '.join(map(str, a[2:]))})"


def lit_name(a, v):
    return ("" if v else "¬") + atom_name(a)


class Form:
    """Форма «G, N, G/N»: атомы, матрица значений по библиотеке, теория."""

    def __init__(self, lib, vocab):
        self.sc, self.lib, self._kept = Scene(vocab), lib, {}
        sc = self.sc
        self.atoms = ([("p", p, sc.G) for p in GROUP_PROPS]
                      + [("p", p, sc.N) for p in SUB_PROPS]
                      + [("p", p, sc.N) for p in GROUP_PROPS]
                      + [("p", p, sc.Q) for p in GROUP_PROPS])
        self.index = {a: i for i, a in enumerate(self.atoms)}
        self.normal = self.index[("p", "normal", sc.N)]
        self.on_q = {i for i, a in enumerate(self.atoms) if a[2] == sc.Q}
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
        rows = np.flatnonzero(self.m[:, list(prem)].all(axis=1) & ~self.m[:, g] & ~self.m[:, g ^ 1])
        if not len(rows):
            return None
        return min(rows, key=lambda r: "×" in self.names[r][0])

    def refuters(self, prem, g, m=None):
        """Строки матрицы (по умолчанию m), где посылки верны, а цель ложна."""
        m = self.m if m is None else m
        neg = g + 1 if g % 2 == 0 else g - 1
        return np.flatnonzero(m[:, list(prem) + [neg]].all(axis=1))

    def lit(self, j):
        """Номер столбца → (атом, значение)."""
        return self.atoms[j // 2], j % 2 == 0

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
        cols = list(prem) + [g ^ 1]
        rows = sorted(self.refuters(prem, g, mat), key=lambda r: "×" in self.names[r][0])[:limit]
        out = {}
        for r in rows:
            key, sub = self.names[r]
            marked = sorted(self.sc.hard_atoms(self.lib, key, sub, (mark,)), key=str)
            hit = []
            for size in range(1, min(len(marked), 3) + 1):
                hit = [k for k in combinations(marked, size)
                       if self.row_keeping(r, frozenset(k), mark)[cols].all()]
                if hit:
                    break
            for k in hit or [marked]:
                out.setdefault(frozenset(self.sc.marked_name(self.lib, key, sub, a, mark) for a in k), r)
        return out


def cover(options):
    """Жадно выбрать факты, чтобы у каждого условия один из его наборов
    (options[i] — список frozenset) был выбран целиком. Возвращает для
    каждого условия выбранный набор: решающий факт условия."""
    chosen, left, out = set(), set(range(len(options))), [None] * len(options)
    while left:
        def gain(c):
            n = sum(1 for i in left if any(t <= chosen | c for t in options[i]))
            return n / max(1, len(c - chosen))
        best = max({c for i in left for c in options[i]}, key=lambda c: (gain(c), sorted(c)))
        chosen |= best
        for i in list(left):
            fit = [t for t in options[i] if t <= chosen]
            if fit:
                out[i] = min(fit, key=lambda t: (len(t), sorted(t)))
                left.discard(i)
    return out


def enumerate_form(form, max_prem, goals=None, m=None):
    """Все условия не длиннее max_prem посылок, которые библиотека не
    опровергает (по матрице m, по умолчанию — только понятными значениями).
    Возвращает (неопровергнутые, без примера)."""
    m = form.e if m is None else m
    n_lit = m.shape[1]
    goal_cols = range(n_lit) if goals is None else goals
    alive, empty = {}, []

    def ok_lits(prem):
        atoms = {j // 2 for j in prem}
        return len(atoms) == len(prem)

    def go(prem, rows, start):
        if prem:
            atoms = {j // 2 for j in prem}
            needs_normal = bool(atoms & form.on_q)
            if not needs_normal or 2 * form.normal in prem:
                if rows.size == 0:
                    empty.append(tuple(prem))
                else:
                    sub = m[rows]
                    for g in goal_cols:
                        if g // 2 in atoms or (g // 2 in form.on_q and 2 * form.normal not in prem):
                            continue
                        neg = g + 1 if g % 2 == 0 else g - 1
                        if not sub[:, neg].any():
                            alive[tuple(prem), g] = int(sub[:, g].sum())
        if len(prem) == max_prem:
            return
        for j in range(start, n_lit):
            if j // 2 in {x // 2 for x in prem}:
                continue
            nxt = rows[m[rows, j]] if prem else np.flatnonzero(m[:, j])
            go(prem + [j], nxt, j + 1)

    go([], np.arange(m.shape[0]), 0)
    return alive, empty


def minimal(alive):
    """Оставить условия, у которых без любой посылки цель опровергается."""
    out = {}
    for (prem, g), support in alive.items():
        if all((tuple(x for x in prem if x != p), g) not in alive for p in prem if len(prem) > 1):
            out[prem, g] = support
    return out


def run(max_prem, lib=None, vocab=None):
    vocab = vocab or Vocab.section("grp")
    if lib is None:
        lib = Library()
        lib.synthesize_products(vocab)
    form = Form(lib, vocab)
    alive, empty = enumerate_form(form, max_prem)
    mins = minimal(alive)
    report = []
    for (prem, g), support in mins.items():
        prem_l = [form.lit(j) for j in prem]
        goal = form.lit(g)
        v = decide(form.sc.T, prem_l, goal, form.sc.s)
        r = {"посылки": [lit_name(*x) for x in prem_l], "цель": lit_name(*goal),
             "запрет": sorted([lit_name(*x) for x in prem_l] + [lit_name(goal[0], not goal[1])]),
             "примеров": support, "вердикт": v.kind,
             "ядро": [lit_name(*x) for x in v.core or []]}
        if v.kind == "неизвестно":
            hint = form.unknown_goal(prem, g)
            if hint is not None:
                key, sub = form.names[hint]
                r["заполнить"] = {"G": key, "N": lib.obj[key]["подгруппы"][sub]["id"], "атом": atom_name(goal[0])}
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
            key, sub = form.names[r["_держится"][1][fact]]
            r["решающий факт"] = sorted(fact)
            r["контрпример"] = {"G": key, "N": lib.obj[key]["подгруппы"][sub]["id"], mark: sorted(fact)}
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
            for i in range(3):
                pair = t[:i] + t[i + 1:]
                by_pair[pair].append(t[i])
        pair, thirds = max(by_pair.items(), key=lambda x: (len(x[1]), x[0]))
        out.append((pair, sorted(thirds)))
        left -= {tuple(sorted(pair + (x,))) for x in thirds}
    return sorted(out, key=lambda x: (-len(x[1]), x[0]))


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--посылок", dest="k", type=int, default=2)
    ap.add_argument("--json", dest="out", help="записать остаток и трудные контрпримеры в JSON")
    ap.add_argument("--короткие", dest="short", action="store_true",
                    help="показать и условия, опровергнутые только коротким доводом")
    a = ap.parse_args()
    form, alive, empty, report = run(a.k)
    tally = Counter(r["вердикт"] for r in report)
    print(f"пар в библиотеке {form.m.shape[0]}, литералов {form.m.shape[1]}", file=sys.stderr)
    print(f"не опровергнуто библиотекой {len(alive)}, из них минимальных {len(report)}: "
          + ", ".join(f"{k} {v}" for k, v in tally.most_common()), file=sys.stderr)
    print(f"посылок без единого примера: {len(empty)}", file=sys.stderr)
    if a.out:
        with open(a.out, "w", encoding="utf-8") as f:
            json.dump({"остаток": [r for r in report if r["вердикт"] == "неизвестно"],
                       "трудный контрпример": [r for r in report if r["вердикт"] == "трудный контрпример"],
                       "короткий довод": [r for r in report if r["вердикт"] == "короткий довод"],
                       "выводится": sum(r["вердикт"] == "выводится" for r in report)},
                      f, ensure_ascii=False, indent=1)
    seen, hints = {}, defaultdict(set)
    for r in report:
        if r["вердикт"] != "неизвестно":
            continue
        t = tuple(r["запрет"])
        seen.setdefault(t, r["примеров"])
        if r.get("заполнить"):
            h = r["заполнить"]
            hints[t].add(f"{h['атом']} у {h['G']} / {h['N']}")
    groups = clusters(list(seen))
    for pair, thirds in groups:
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
        for r in report:
            if r["вердикт"] == kind:
                groups[tuple(r["решающий факт"])].append(r)
        ranked = sorted(groups.items(), key=lambda x: (-len(x[1]), x[0]))
        if kind == "короткий довод" and not a.short:
            if ranked:
                print(f"скрыто условий с коротким доводом: {tally[kind]}, решающих фактов {len(ranked)}: "
                      + ", ".join(f"{' & '.join(f)} ({len(rs)})" for f, rs in ranked)
                      + " (показать: --короткие)", file=sys.stderr)
            continue
        for fact, rs in ranked:
            print(f"{kind}: {' & '.join(fact)} — условий {len(rs)}")
            for r in rs:
                c = r["контрпример"]
                print(f"    {', '.join(r['посылки'])} ⇒ {r['цель']}   [{c['G']} / {c['N']}]")


if __name__ == "__main__":
    main()
