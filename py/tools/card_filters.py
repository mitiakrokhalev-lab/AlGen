"""Сверка карточек архива с фильтрами перебора, которым не нужна таблица.

Для каждой машинной карточки (условие + цель) проверяется, что её условие не
снимут фильтры перебора:
* «о части переменных» (enumerate.about_all_vars, с учётом зависимостей сортов);
* покрытие верхних термов (table.need_tops): каждого верхнего терма касается литерал;
* замкнутые литералы (все термы — константы): они не перебираются.
Для сравнения считается и старый фильтр «о части переменных» (равенство множеств
переменных без зависимостей). Карточка, не прошедшая фильтр, — либо утверждение
меньшей базы (тогда оно должно найтись там), либо дыра.

    cd py && ALGEN_SIZE=2 python3 tools/card_filters.py [--все]
"""
import glob
import json
import os
import sys
from pathlib import Path

os.environ.setdefault("ALGEN_SIZE", "2")
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from algen import enumerate as E  # noqa: E402
from algen import table as T  # noqa: E402
from algen.etalon import scheme  # noqa: E402
from algen.logic import App, Var, Vocab  # noqa: E402

ROOT = Path(__file__).resolve().parents[2]


def ground(t):
    return isinstance(t, App) and all(ground(a) for a in t.args)


def terms_of(a):
    return [x for x in a[2:] if not isinstance(x, (str, int, bool))]


def check(c, vocab):
    g, prem, goal = scheme(vocab, c)
    lits = list(prem) + [goal]
    allvars = {t for t in g.terms if isinstance(t, Var)}
    old_ok = set().union(*(E.atom_vars(a, g) for a, _ in lits)) == allvars
    new_ok = E.about_all_vars(lits, g)
    ts = {t for a, _ in lits for t in terms_of(a)}
    sub = set()
    for t in ts:
        sub |= T.closure(g, [t])
    tops = T.need_tops(g, (sub | allvars) - set())
    touched = {t for a, _ in lits for t in terms_of(a)}
    untouched = [str(t) for t in tops if t not in touched]
    grounded = [E.atom_name(a) for a, _ in lits if terms_of(a) and all(ground(x) for x in terms_of(a))]
    s = len(set().union(*(T.app_nodes(t) for t in ts))) if ts else 0
    return {"старый фильтр": old_ok, "новый фильтр": new_ok, "не касается верхних": untouched,
            "замкнутые литералы": grounded, "s": s, "k": len(prem),
            "переменные": sorted(f"{t}:{g.terms[t].sort}" for t in allvars)}


def main():
    vocab = Vocab.section("grp")
    rows, errs = [], 0
    for p in sorted(glob.glob(str(ROOT / "data" / "archive" / "grp" / "*.jsonl"))):
        for line in open(p, encoding="utf-8"):
            if not line.strip():
                continue
            c = json.loads(line)
            if not c.get("условие") or not c.get("цель") or c.get("уровень") == "определение":
                continue
            try:
                r = check(c, vocab)
            except Exception as e:  # формулы, параметры — не этот путь
                errs += 1
                continue
            rows.append((c["id"], r))
    print(f"машинных карточек разобрано {len(rows)}, не разобрано этим путём {errs}")
    lost_old = [i for i, r in rows if not r["старый фильтр"]]
    lost_new = [i for i, r in rows if not r["новый фильтр"]]
    print(f"снимались старым фильтром «о части переменных»: {len(lost_old)}; новым: {len(lost_new)}")
    for i, r in rows:
        if r["старый фильтр"] != r["новый фильтр"] or not r["новый фильтр"] or r["не касается верхних"] or r["замкнутые литералы"]:
            if "--все" in sys.argv or r["старый фильтр"] != r["новый фильтр"] or r["не касается верхних"] or r["замкнутые литералы"]:
                print(i, json.dumps(r, ensure_ascii=False))


if __name__ == "__main__":
    main()
