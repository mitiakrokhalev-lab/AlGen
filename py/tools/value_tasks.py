"""Задачи-значения: какие недостающие значения таблицы решают неизвестные условия выборки.

Запуск — как `python3 -m algen.table перебор …` (те же аргументы, ALGEN_SAMPLE, ALGEN_COMPRESS):

    python3 -B -m tools.value_tasks перебор G --каталог ../tab --выход ../out --схемы SID …

Модуль подменяет сбор статистики выборки (enumerate._sample_stats) расширенной версией и
вызывает table.main(). Файлы algen/ не меняются — отпечаток таблиц прежний, подходят готовые
таблицы; вердикты, сжатие и прежние поля сводки те же, добавляется поле «задачи-значения».

Неизвестное условие выборки (запрет: посылки и отрицание цели) по строкам библиотеки:
  A — есть строка, где ни один литерал запрета не ложен и неизвестен ровно один: значение этого
      литерала в этой строке решает судьбу условия (истинно — строка опровергает условие);
  B — таких строк нет, но есть строки без ложных литералов с ⩾ 2 неизвестными;
  C — в каждой строке какой-то литерал запрета ложен: данных хватает, условие верно на всех
      примерах (ждёт правила, нового примера или это вопрос).
Значение — form.value_name(строка, атом): у построенных произведений — значение множителя, так
что одно значение группы библиотеки считается один раз. Сводка: различных значений, условий на
одно значение, жадное покрытие условий A, рост числа значений с размером выборки (для оценки
по всей схеме), опора условий C; отдельно — для оставленных после сжатия внутри схемы.
Полный список значений с числом условий — в <выход>/values-<схема>.json.gz.
"""
import gzip
import json
import os
import sys
import time
from collections import Counter
from pathlib import Path

import numpy as np

CAP = 2000  # строк-кандидатов на условие, которым даётся имя (остальные не именуются)
KEEP = 200  # значений условия, которые хранятся для подсчёта покрытия (память)
SECONDS = float(os.environ.get("VALUE_TASKS_SECONDS", "1800"))  # срок сводки на схему
GROWTH = (1000, 2000, 5000, 10000, 20000, 50000, 100000)


def _arg(name):
    a = sys.argv
    return a[a.index(name) + 1] if name in a and a.index(name) + 1 < len(a) else None


def classify(form, cols):
    """(вид, {(строка, столбец)} однозначных кандидатов, строк с ⩾ 2 неизвестными, опровергающих)."""
    _, P, valid = form._bits(form.m)
    cols = list(cols) + list(form.fixed)
    ok = valid.copy()
    for c in cols:
        ok &= ~P[c ^ 1]  # ни один литерал не ложен
    one, two = np.zeros_like(valid), np.zeros_like(valid)
    for c in cols:
        u = ~P[c] & ~P[c ^ 1]
        two |= one & u
        one |= u
    allt = ok & ~one  # все литералы верны — такая строка опровергала бы условие
    single = ok & one & ~two
    multi = ok & two
    pairs = []
    if single.any():
        for c in cols:
            rest = ok & ~P[c] & ~P[c ^ 1]
            for c2 in cols:
                if c2 != c:
                    rest &= P[c2]
            if rest.any():
                for r in form._rows(form.m, rest):
                    pairs.append((int(r), int(c)))
    n_multi = int(np.unpackbits(multi.view(np.uint8)).sum())
    n_allt = int(np.unpackbits(allt.view(np.uint8)).sum())
    kind = "A" if pairs else ("B" if n_multi else "C")
    return kind, pairs, n_multi, n_allt


def _atom(form, c):
    a = form.atoms[c // 2]
    return form.lits(c)[0][0] if a[0] == "pair" else form.lit(c)[0]


def _row_object(form, r):
    """Объект строки: ключ записанной группы библиотеки или «×» для построенного произведения."""
    if hasattr(form, "row_object"):
        return form.row_object(r)
    envs = getattr(form, "envs", None)
    if envs is None:
        return "?"
    for im in envs[r].values():
        if im and im[0] == "obj":
            return "×" if form.lib.obj[im[1]].get("синтез") else im[1]
    return "?"


def _root(form, r, c):
    """Корень знания: (шаблон атома, объект строки). У построенных произведений объект «×» —
    одна задача-правило на шаблон для всех произведений."""
    from algen.enumerate import atom_name
    return (atom_name(_atom(form, c)), _row_object(form, r))


def _cells_b(form, cols, limit=CAP):
    """Клетки неизвестных литералов в строках без ложных литералов с ⩾ 2 неизвестными (вид B)."""
    _, P, valid = form._bits(form.m)
    cols = list(cols) + list(form.fixed)
    ok = valid.copy()
    for c in cols:
        ok &= ~P[c ^ 1]
    one, two = np.zeros_like(valid), np.zeros_like(valid)
    for c in cols:
        u = ~P[c] & ~P[c ^ 1]
        two |= one & u
        one |= u
    multi = ok & two
    cells = []
    for c in cols:
        rows = multi & ~P[c] & ~P[c ^ 1]
        if rows.any():
            for r in form._rows(form.m, rows)[:limit]:
                cells.append((int(r), int(c)))
    return cells


def _hitting(sets):
    """Жадное покрытие (ленивая куча): сколько корней, чтобы у каждого условия был хотя бы
    один выбранный корень."""
    import heapq
    by = {}
    for j, x in enumerate(sets):
        for v in x:
            by.setdefault(v, set()).add(j)
    alive = {j for j, x in enumerate(sets) if x}
    heap = [(-len(js), n, v) for n, (v, js) in enumerate(by.items())]
    heapq.heapify(heap)
    picked = 0
    while alive and heap:
        neg, n, v = heapq.heappop(heap)
        cur = len(by[v] & alive)
        if cur == 0:
            continue
        if cur < -neg:
            heapq.heappush(heap, (-cur, n, v))
            continue
        alive -= by[v]
        picked += 1
    return picked


def knowledge(form, report):
    """Генератор от знаний против прежнего «по вопросам» на тех же условиях отчёта.

    Было: неизвестные условия, оставленные после сжатия, — вопросы человеку.
    Стало: (1) условия вида C (данных хватает, верно на всех примерах) — вопросы человеку;
    (2) условия A и B ждут значений: их заменяют корни знаний (шаблон атома × записанная
    группа; у произведений — шаблон × «×», задача-правило), очередь машине/агентам."""
    out = {}
    for label, rows in (("все неизвестные", [r for r in report if r["вердикт"] == "неизвестно"]),
                        ("оставленные после сжатия",
                         [r for r in report if r["вердикт"] == "неизвестно" and not r.get("свёрнута")])):
        kinds, roots, sets, t0, stopped = Counter(), Counter(), [], time.time(), None
        for i, r in enumerate(rows, 1):
            if time.time() - t0 > SECONDS:
                stopped = i - 1
                break
            cols = r.get("_cols") or []
            kind, pairs, _n_multi, _n_allt = classify(form, cols)
            kinds[kind] += 1
            if kind == "C":
                continue
            cells = pairs[:CAP] if kind == "A" else _cells_b(form, cols)
            rs = {_root(form, x, c) for x, c in cells}
            sets.append(rs)
            roots.update(rs)
        real = sum(1 for (_p, o) in roots if o != "×")
        out[label] = {
            "условий": len(rows), "разобрано": stopped if stopped is not None else len(rows),
            "по видам": dict(kinds),
            "вопросов человеку (C)": kinds.get("C", 0),
            "ждут знаний (A + B)": kinds.get("A", 0) + kinds.get("B", 0),
            "корней знаний всего": len(roots),
            "из них значений записанных групп": real,
            "из них правил для произведений (шаблон × «×»)": len(roots) - real,
            "шаблонов атомов": len({p for p, _o in roots}),
            "корней, чтобы затронуть все условия A/B (жадно)": _hitting(sets),
            "топ корней": [[f"{p} у {o}", n] for (p, o), n in roots.most_common(30)],
            "_корни": roots}
    return out


def _name(form, r, c):
    a = form.atoms[c // 2]
    atom = form.lits(c)[0][0] if a[0] == "pair" else form.lit(c)[0]
    return form.value_name(r, atom)


def value_tasks(form, report):
    """Сводка задач-значений по неизвестным строкам отчёта (у строк есть «_cols»)."""
    out = {}
    for label, rows in (("все неизвестные", [r for r in report if r["вердикт"] == "неизвестно"]),
                        ("оставленные после сжатия",
                         [r for r in report if r["вердикт"] == "неизвестно" and not r.get("свёрнута")])):
        kinds, sizes, counts, capped, refuting = Counter(), Counter(), Counter(), 0, 0
        growth, seen, support_c = {}, set(), Counter()
        per_cond, t0, stopped = [], time.time(), None
        for i, r in enumerate(rows, 1):
            if time.time() - t0 > SECONDS:
                stopped = i - 1
                break
            cols = r.get("_cols") or []
            kind, pairs, n_multi, n_allt = classify(form, cols)
            refuting += bool(n_allt)
            kinds[kind] += 1
            if kind == "A":
                if len(pairs) > CAP:
                    capped += 1
                    pairs = pairs[:CAP]
                names = {_name(form, x, c) for x, c in pairs}
                per_cond.append(set(list(names)[:KEEP]) if len(names) > KEEP else names)
                counts.update(names)
                seen |= names
                n = len(names)
                sizes["1" if n == 1 else "2–5" if n <= 5 else "6–20" if n <= 20 else "21–100" if n <= 100 else ">100"] += 1
            elif kind == "C":
                s = r.get("примеров")
                support_c["0" if not s else "1–2" if s <= 2 else "3–10" if s <= 10 else ">10"] += 1
            if i in GROWTH:
                growth[str(i)] = len(seen)
        growth[str(stopped if stopped is not None else len(rows))] = len(seen)
        # покрытие по частоте: значения по убыванию числа условий; сколько первых значений
        # затрагивают 50/80/95/100 % условий A (затронуто — хотя бы одно значение условия известно)
        cover, hit, done, marks = {}, [False] * len(per_cond), 0, (50, 80, 95, 100)
        by_val = {}
        for j, names in enumerate(per_cond):
            for v in names:
                by_val.setdefault(v, []).append(j)
        # порядок — по числу условий среди хранимых наборов (наборы условия урезаны до KEEP:
        # значение из counts может в них не попасть — ошибка pilot-10, 13.11)
        order = Counter(x for names in per_cond for x in names)
        for k, (v, _n) in enumerate(order.most_common(), 1):
            for j in by_val[v]:
                if not hit[j]:
                    hit[j] = True
                    done += 1
            for m in marks:
                if f"{m} %" not in cover and per_cond and done * 100 >= m * len(per_cond):
                    cover[f"{m} %"] = k
            if done == len(per_cond):
                break
        out[label] = {"условий": len(rows), "разобрано": stopped if stopped is not None else len(rows),
                      "по видам": dict(kinds), "опровергающих строк (должно быть 0)": refuting,
                      "различных значений (A)": len(seen), "значений на условие A": dict(sizes),
                      "кандидатов обрезано": capped, "рост значений с выборкой": growth,
                      "покрытие условий A первыми значениями": cover, "опора условий C": dict(support_c),
                      "_значения": counts}
    return out


def install():
    from algen import enumerate as E
    original = E._sample_stats

    def stats(form, mins, report, total):
        res = original(form, mins, report, total)
        kn = knowledge(form, report)
        full_roots = {k: v.pop("_корни") for k, v in kn.items()}
        res["знания"] = kn
        full = {}
        if os.environ.get("VALUE_TASKS_NAMES") == "1":  # прежний подсчёт имён значений (pilot-11)
            vt = value_tasks(form, report)
            full = {k: v.pop("_значения") for k, v in vt.items()}
            res["задачи-значения"] = vt
            res["задачи-значения"]["топ значений"] = Counter(full["все неизвестные"]).most_common(40)
        out, sid = _arg("--выход"), _arg("--схемы")
        if out and sid and "," not in sid:
            Path(out).mkdir(parents=True, exist_ok=True)
            if full:
                with gzip.open(Path(out) / f"values-{sid}.json.gz", "wt", encoding="utf-8") as f:
                    json.dump({k: dict(v) for k, v in full.items()}, f, ensure_ascii=False)
            with gzip.open(Path(out) / f"roots-{sid}.json.gz", "wt", encoding="utf-8") as f:
                json.dump({k: [[p, o, n] for (p, o), n in v.items()] for k, v in full_roots.items()},
                          f, ensure_ascii=False)
        return res

    E._sample_stats = stats


def main():
    install()
    from algen import table
    sys.exit(table.main())


if __name__ == "__main__":
    main()
