"""Архив фактов: прогон карточек через генератор и проверка покрытия.

Карточка архива (data/archive/<раздел>/<тема>.jsonl) — одна известная задача:
формулировка для человека, ответ, обоснование, ссылка и, если словарь
позволяет, машинная запись (условие и цель в нотации телескопа). Формат и
классификация — docs/архив.md.

Каждая карточка должна попасть ровно в одну корзину:

* словарь — определение или равносильная переформулировка;
* закрыто генератором — вывод из базы правил или понятный контрпример из
  библиотеки; контрпример, который держится на значении с пометкой «трудно»
  (само значение — теорема или требует идеи), задачу не закрывает;
* факт — генератор не закрыл, ответ известен; это и есть содержимое архива;
* открыто — ответ неизвестен;
* КРАСНЫЙ ФЛАГ — задача не записывается в словаре, или генератор ответил не
  так, как ожидалось по уровню карточки. Список флагов — мерило покрытия.

    cd py && python3 -m algen.archive ../data/archive/grp/ф-а.jsonl
"""

import argparse
import json
import sys
from collections import Counter

from .etalon import Unsupported, judge, scheme
from .library import Library, Search
from .logic import Theory, Vocab, decide

# Уровни, которые генератор обязан закрыть сам.
MUST_CLOSE = {"правило", "следствие", "понятный контрпример"}


def lit_str(a, v):
    return f"{'' if v else '¬'}{a[1]}({', '.join(map(str, a[2:]))})"


def run_card(c, vocab, lib):
    out = {"id": c["id"]}
    if c["уровень"] == "определение":
        return {**out, "корзина": "словарь"}
    if not c.get("условие"):
        return {**out, "корзина": "КРАСНЫЙ ФЛАГ",
                "почему": "не записывается: нет в словаре " + ", ".join(c.get("вне_словаря", ["?"]))}
    try:
        g, prem, goal = scheme(vocab, c)
    except Unsupported as e:
        return {**out, "корзина": "КРАСНЫЙ ФЛАГ", "почему": f"не разбирается: {e}"}
    theory = Theory(g, grow=1)
    v = decide(theory, prem, goal)
    kind, detail = v.kind, ""
    if kind == "выводится":
        used = {a for a, _ in v.core or []}
        extra = [lit_str(a, val) for a, val in prem if a not in used]
        detail = "ядро: " + (", ".join(lit_str(a, val) for a, val in v.core) or "—")
        if extra:
            detail += "; лишние посылки: " + ", ".join(extra)
    elif kind == "неизвестно":
        found = Search(g, theory, lib).witnesses(prem, goal, limit=10)
        if found:
            # Понятный контрпример лучше: тот, что не держится на теоремах.
            w = min(found, key=lambda w: len(w["трудно"]))
            kind = "опровергается"
            detail = "контрпример: " + ", ".join(f"{k} = {x}" for k, x in w["подстановка"].items())
            if w["трудно"]:
                hard = "; держится на " + ", ".join(w["трудно"])
                out.update(вердикт=kind, детали=detail + hard)
                return {**out, "корзина": "факт" if c["ответ"] == "ложно" else "КРАСНЫЙ ФЛАГ"}
    out.update(вердикт=kind, детали=detail)
    if c["ответ"] == "открыто":
        verdict = judge("открыто", kind)
    else:
        verdict = judge(c["ответ"], kind)
    if verdict == "ОШИБКА":
        return {**out, "корзина": "КРАСНЫЙ ФЛАГ", "почему": f"генератор ответил «{kind}», а ответ «{c['ответ']}»"}
    if kind in ("выводится", "опровергается"):
        return {**out, "корзина": "закрыто генератором"}
    if c["ответ"] == "открыто":
        return {**out, "корзина": "открыто"}
    if c["уровень"] in MUST_CLOSE:
        return {**out, "корзина": "КРАСНЫЙ ФЛАГ",
                "почему": f"уровень «{c['уровень']}», а генератор не закрыл: не хватает правила или примера"}
    return {**out, "корзина": "факт"}


def run(cards):
    vocab = Vocab.section("grp")
    lib = Library()
    return [run_card(c, vocab, lib) for c in cards]


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("cards")
    ap.add_argument("--json", dest="as_json", action="store_true")
    a = ap.parse_args()
    with open(a.cards, encoding="utf-8") as f:
        cards = [json.loads(line) for line in f if line.strip()]
    report = run(cards)
    if a.as_json:
        json.dump(report, sys.stdout, ensure_ascii=False, indent=1)
        return
    for c, r in zip(cards, report):
        tail = r.get("почему") or f"{r.get('вердикт', '')}; {r.get('детали', '')}".strip("; ")
        print(f"{c['id']:6} {c['уровень']:20} {r['корзина']:20} {tail}")
    print("\n" + ", ".join(f"{k} {v}" for k, v in Counter(r["корзина"] for r in report).most_common()))


if __name__ == "__main__":
    main()
