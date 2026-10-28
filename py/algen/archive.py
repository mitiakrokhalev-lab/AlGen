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
* короткий довод — контрпример держится на значении с пометкой «короткий
  довод» (несколько строк, но не учебный факт); в выдаче скрыто, показать —
  флаг --короткие;
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
from .identities import FREE_NILPOTENT, ParseError, holds, parse, show_poly, show_word, variety
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
    if c.get("тождество"):
        return finish(c, out, *identity(c, prem))
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
            w = min(found, key=lambda w: (len(w["трудно"]), len(w["короткий довод"])))
            kind = "опровергается"
            detail = "контрпример: " + ", ".join(f"{k} = {x}" for k, x in w["подстановка"].items())
            for mark, bucket in (("трудно", "факт"), ("короткий довод", "короткий довод")):
                if w[mark]:
                    out.update(вердикт=kind, детали=detail + "; держится на " + ", ".join(w[mark]))
                    return {**out, "корзина": bucket if c["ответ"] == "ложно" else "КРАСНЫЙ ФЛАГ"}
    return finish(c, out, kind, detail)


def identity(c, prem):
    """Тождество в элементах: решается в относительно свободной группе."""
    lev, rest = variety(prem)
    conv = c.get("коммутатор", "x⁻¹y⁻¹xy")
    lhs, rhs = c["тождество"].split("=")
    try:
        ok, wit = holds(parse(lhs, conv), parse(rhs, conv), lev)
    except ParseError as e:
        return "неизвестно", f"не разбирается: {e}"
    where = "все группы" if lev is None else f"ступень нильпотентности ⩽ {lev}"
    if ok:
        return "выводится", f"верно в относительно свободной группе ({where})"
    props = {a[1] for a, v in rest if a[0] == "p" and v}
    if (any(not (a[0] == "p" and a[1] in FREE_NILPOTENT and v) for a, v in rest)
            or (props & {"finite", "periodic"} and "torsion-free" in props)):
        return "неизвестно", f"неверно в относительно свободной группе ({where}), но посылки " + \
            ", ".join(lit_str(a, v) for a, v in rest) + " она может не выполнять"
    shown = show_word(wit) if lev is None else show_poly(wit) + " ≠ 0 в алгебре Магнуса"
    return "опровергается", f"контрпример — относительно свободная группа ({where}): u⁻¹v ↦ {shown}"


def finish(c, out, kind, detail):
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
    ap.add_argument("--короткие", dest="short", action="store_true",
                    help="показать и карточки корзины «короткий довод»")
    a = ap.parse_args()
    with open(a.cards, encoding="utf-8") as f:
        cards = [json.loads(line) for line in f if line.strip()]
    report = run(cards)
    if a.as_json:
        json.dump(report, sys.stdout, ensure_ascii=False, indent=1)
        return
    for c, r in zip(cards, report):
        if r["корзина"] == "короткий довод" and not a.short:
            continue
        tail = r.get("почему") or f"{r.get('вердикт', '')}; {r.get('детали', '')}".strip("; ")
        print(f"{c['id']:6} {c['уровень']:20} {r['корзина']:20} {tail}")
    tally = Counter(r["корзина"] for r in report)
    print("\n" + ", ".join(f"{k} {v}" for k, v in tally.most_common()))
    if tally["короткий довод"] and not a.short:
        print(f"скрыто карточек с коротким доводом: {tally['короткий довод']} (показать: --короткие)")


if __name__ == "__main__":
    main()
