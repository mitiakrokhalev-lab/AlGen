"""Отчёт о пробелах: какие атомы держат вопросы живыми.

Вопрос остаётся, когда его не опровергла библиотека и не вывела теория. Атом
запрета, у которого в библиотеке мало значений и в теории мало правил, держит
сразу много вопросов. Отчёт считает по оставленным вопросам образцы атомов
(свойство и форма терма без имён переменных: «primitive(regular-act(·))») и
выдаёт очередь: какой пробел закрыть теоремой или данными, чтобы снять больше
вопросов.

    python3 -m algen.gaps <каталог схем> [--сжатие cb.json] [--выход отчёт.md]

Каталог схем — записи перебора (*.json). С --сжатие считаются только вопросы,
оставленные сжатием по схемам, и отдельно — «вне фона».
"""

import argparse
import collections
import glob
import json
import os
import re

_LIT = re.compile(r"^(¬?)([a-z0-9-]+)\((.*)\)$")
_VAR = re.compile(r"(?<![\w-])([A-Z][A-Za-z0-9]*)(?![\w(-])")


def shape(term):
    """Форма терма без имён переменных: center(G) → center(·), incl(G, center(G)) →
    incl(·, center(·)). Числа (num:5()) остаются."""
    return _VAR.sub("·", term)


def pattern(lit):
    """Образец атома литерала запрета (без знака) или None."""
    m = _LIT.match(lit.strip())
    if not m:
        return None
    return f"{m.group(2)}({shape(m.group(3))})"


def load(dirname, compressed=None):
    """[(№, запрет, вне фона?)] — оставленные вопросы каталога (или сжатия)."""
    Q = {}
    for f in sorted(glob.glob(os.path.join(dirname, "*.json"))):
        try:
            r = json.load(open(f))
        except (OSError, ValueError):
            continue
        if not isinstance(r, dict) or "id" not in r:
            continue
        for q in r.get("оставленные вопросы", []):
            Q[f"{r['id']}:{q['№']}"] = q["запрет"]
    if compressed is None:
        return [(k, z, False) for k, z in Q.items()], 0
    d = json.load(open(compressed))
    out = d.get("особые", {})
    keep = d.get("оставлено", [])
    missing = sum(k not in Q for k in keep)
    return [(k, Q[k], k in out) for k in keep if k in Q], missing


def report(qs, top=40, examples=2):
    """Строки отчёта (markdown): очередь образцов по числу вопросов."""
    by = collections.defaultdict(list)
    for k, z, outside in qs:
        for p in {pattern(l) for l in z} - {None}:
            by[p].append((k, z, outside))
    rows = sorted(by.items(), key=lambda kv: (-len(kv[1]), kv[0]))
    n_out = sum(o for _, _, o in qs)
    lines = [f"Вопросов {len(qs)} (из них вне фона {n_out}); образцов атомов {len(by)}.", "",
             "| № | образец | вопросов | вне фона | пример |", "|---|---|---|---|---|"]
    for i, (p, lst) in enumerate(rows[:top], 1):
        ex = "; ".join(" & ".join(z) for _, z, _ in lst[:examples])
        lines.append(f"| {i} | `{p}` | {len(lst)} | {sum(o for *_, o in lst)} | {ex} |")
    return lines, rows


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("каталог")
    ap.add_argument("--сжатие", dest="comp")
    ap.add_argument("--выход", dest="out")
    ap.add_argument("--первые", dest="top", type=int, default=40)
    a = ap.parse_args(argv)
    qs, missing = load(a.каталог, a.comp)
    lines, rows = report(qs, a.top)
    head = ["# Пробелы: какие атомы держат вопросы", ""]
    if missing:
        head += [f"**Внимание:** {missing} оставленных сжатием вопросов не найдены в каталоге схем.", ""]
    text = "\n".join(head + lines) + "\n"
    if a.out:
        open(a.out, "w").write(text)
        json.dump([{"образец": p, "вопросов": len(l), "вне фона": sum(o for *_, o in l),
                    "вопросы": [k for k, _, _ in l]} for p, l in rows],
                  open(os.path.splitext(a.out)[0] + ".json", "w"), ensure_ascii=False, indent=1)
    print(text)


if __name__ == "__main__":
    main()
