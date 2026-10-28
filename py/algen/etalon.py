"""Прогон эталона data/etalon/эталон.jsonl через вывод на SAT.

Эталон — мерило генератора (docs/ПЕРЕДЕЛКА.md): факты с известным ответом.
Для каждого факта вывод (algen.logic) даёт вердикт, и он сравнивается с
ответом:

* «верно» должно выводиться, «ложно» — опровергаться;
* «открыто» не должно ни выводиться, ни опровергаться;
* вывод верного или опровержение ложного — ОШИБКА базы, а не промах.

Вывод сам по себе опровергает только то, что противоречит правилам. Ложное
обычно закрывается контрпримером (этап 5), поэтому «ложно → неизвестно» здесь
считается промахом, а не ошибкой.

    cd py && python3 -m algen.etalon
"""

import argparse
import json
import re
import sys
from collections import Counter

from .logic import DATA, Graph, Theory, Vocab, decide

ETALON = DATA / "etalon" / "эталон.jsonl"
SORTS = {"grp": {"Grp": ("Grp.obj", None), "Sub": ("Grp.sub", "ambient")}}
# Короткие обозначения конструкций в записи эталона.
OPS = {"grp": {"Z": "center", "core": "core", "Inn": "inn"}}


class Unsupported(Exception):
    pass


def split_top(s, sep):
    """Разбить по sep вне скобок."""
    out, depth, cur = [], 0, ""
    for ch in s:
        depth += ch == "("
        depth -= ch == ")"
        if ch == sep and depth == 0:
            out.append(cur)
            cur = ""
        else:
            cur += ch
    return [x.strip() for x in out + [cur] if x.strip()]


def term(g, s, names, section):
    s = s.strip()
    if s in names:
        return names[s]
    parts = split_top(s, "/")
    if len(parts) == 2:
        t = g.make("quotient", [term(g, p, names, section) for p in parts])
    else:
        m = re.fullmatch(r"(\w[\w-]*)\((.*)\)", s)
        if not m or m.group(1) not in OPS[section]:
            raise Unsupported(f"терм {s!r}")
        t = g.make(OPS[section][m.group(1)],
                   [term(g, a, names, section) for a in split_top(m.group(2), ",")])
    if t is None:
        raise Unsupported(f"терм {s!r} не строится")
    return g.given(t)


def literal(g, s, names, section):
    s = s.strip()
    value = not s.startswith("¬")
    m = re.fullmatch(r"([\w-]+)\((.*)\)", s.lstrip("¬").strip())
    if not m:
        raise Unsupported(f"литерал {s!r}")
    args = [term(g, a, names, section) for a in split_top(m.group(2), ",")]
    if m.group(1) in g.v.props and len(args) == 1:
        return ("p", m.group(1), args[0]), value
    if m.group(1) in g.v.rels:
        return ("r", m.group(1), *args), value
    raise Unsupported(f"нет в словаре: {m.group(1)}")


def scheme(vocab, fact):
    """Запись эталона → граф, посылки, цель."""
    section = fact["раздел"]
    if section not in SORTS:
        raise Unsupported(f"раздел {section}")
    g, names, prem = Graph(vocab), {}, []
    for decl in fact["условие"].split(";"):
        head, _, lits = decl.partition("|")
        m = re.fullmatch(r"\s*∀\s*(\w+)\s*:\s*(\w+)(?:\((\w+)\))?\s*", head)
        if not m:
            raise Unsupported(f"объявление {head!r}")
        name, sort, parent = m.groups()
        if sort not in SORTS[section]:
            raise Unsupported(f"сорт {sort}")
        s, link = SORTS[section][sort]
        names[name] = g.var(name, s, **({link: names[parent]} if parent else {}))
        prem += [literal(g, x, names, section) for x in split_top(lits, ",")]
    goal = literal(g, fact["цель"], names, section)
    return g, prem, goal


EXPECT = {"верно": "выводится", "ложно": "опровергается", "открыто": "неизвестно"}
WRONG = {"верно": {"опровергается", "противоречие"}, "ложно": {"выводится", "противоречие"},
         "открыто": {"выводится", "опровергается", "противоречие"}}


def judge(answer, kind):
    if kind == EXPECT[answer]:
        return "закрыто верно" if answer != "открыто" else "дошло до остатка"
    if kind in WRONG[answer]:
        return "ОШИБКА"
    return "промах"


def run(facts, grow=1):
    vocabs, report = {}, []
    for f in facts:
        row = {"id": f["id"], "ответ": f["ответ"]}
        try:
            v = vocabs.get(f["раздел"]) or vocabs.setdefault(f["раздел"], Vocab.section(f["раздел"]))
            g, prem, goal = scheme(v, f)
        except (Unsupported, FileNotFoundError) as e:
            report.append({**row, "итог": "не разбирается", "почему": str(e)})
            continue
        verdict = decide(Theory(g, grow=grow), prem, goal)
        row.update(итог=judge(f["ответ"], verdict.kind), вердикт=verdict.kind,
                   ядро=[f"{'' if val else '¬'}{a[1]}({', '.join(map(str, a[2:]))})"
                         for a, val in verdict.core or []])
        if verdict.kind == "выводится" and len(verdict.core) < len(prem):
            row["лишние посылки"] = len(prem) - len(verdict.core)
        report.append(row)
    return report


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--эталон", dest="etalon", default=str(ETALON))
    ap.add_argument("--достройка", dest="grow", type=int, default=1)
    ap.add_argument("--json", dest="as_json", action="store_true")
    a = ap.parse_args()
    with open(a.etalon, encoding="utf-8") as f:
        facts = [json.loads(line) for line in f if line.strip()]
    report = run(facts, a.grow)
    if a.as_json:
        json.dump(report, sys.stdout, ensure_ascii=False, indent=1)
        return
    for r in report:
        extra = r.get("почему") or f"{r['вердикт']}; ядро: {', '.join(r['ядро']) or '—'}"
        print(f"{r['id']:10} {r['ответ']:8} {r['итог']:17} {extra}")
    print("\n" + ", ".join(f"{k} {v}" for k, v in Counter(r["итог"] for r in report).most_common()))


if __name__ == "__main__":
    main()
