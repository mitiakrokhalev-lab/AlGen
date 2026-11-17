"""Очередь знаний между схемами: объединение корней знаний схем (выдача ALGEN_KNOWLEDGE=1).

    python3 -B -m tools.knowledge_queue КАТАЛОГ [--выход queue.json] [--топ 40]

Читает в КАТАЛОГЕ (рекурсивно) <схема>.knowledge.json.gz (генератор, algen/knowledge.py) или
roots-<схема>.json.gz (замер tools/value_tasks.py) и сводки схем <схема>.json. Корень — (шаблон
атома, объект): объект — записанная группа (значение — задача агенту: посчитать или найти в
литературе) или «×» (правило для произведений — задача-правило). Счёт корня — сумма по схемам
числа оставленных после сжатия запретов, которые ждут этого корня; схем — в скольких схемах он
нужен. Отдельно — по группам (сколько запретов ждут значений этой группы) и по шаблонам.
"""
import argparse
import gzip
import json
import sys
from collections import Counter, defaultdict
from pathlib import Path

LABEL = "оставленные после сжатия"


def load(root):
    files = sorted(Path(root).rglob("*.knowledge.json.gz")) + sorted(Path(root).rglob("roots-*.json.gz"))
    per_root, schemes = Counter(), defaultdict(set)
    for f in files:
        sid = f.name.replace(".knowledge.json.gz", "").replace("roots-", "").replace(".json.gz", "")
        x = json.load(gzip.open(f, "rt", encoding="utf-8"))
        for p, o, n in x.get(LABEL, []):
            per_root[(p, o)] += n
            schemes[(p, o)].add(sid)
    return files, per_root, schemes


def queue(per_root, schemes, top=40):
    by_group, by_pattern, rules = Counter(), Counter(), Counter()
    for (p, o), n in per_root.items():
        if "×" in o.split(", "):
            rules[p] += n
        else:
            by_group[o] += n
        by_pattern[p] += n
    order = sorted(per_root.items(), key=lambda x: (-x[1], x[0]))
    return {
        "корней": len(per_root),
        "значений записанных групп": sum(1 for (p, o) in per_root if "×" not in o.split(", ")),
        "правил для произведений": len(rules),
        "групп с недостающими значениями": len(by_group),
        "шаблонов": len(by_pattern),
        "в нескольких схемах": sum(1 for k in per_root if len(schemes[k]) > 1),
        "топ корней": [{"корень": f"{p} у {o}", "запретов": n, "схем": len(schemes[(p, o)])}
                       for (p, o), n in order[:top]],
        "топ групп": [{"группа": g, "запретов": n} for g, n in by_group.most_common(top)],
        "топ правил": [{"шаблон": p, "запретов": n} for p, n in rules.most_common(top)],
        "топ шаблонов": [{"шаблон": p, "запретов": n} for p, n in by_pattern.most_common(top)],
    }


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("каталог")
    ap.add_argument("--выход")
    ap.add_argument("--топ", type=int, default=40)
    a = ap.parse_args(argv)
    files, per_root, schemes = load(a.каталог)
    q = queue(per_root, schemes, a.топ)
    q["файлов"] = len(files)
    if a.выход:
        Path(a.выход).write_text(json.dumps(q, ensure_ascii=False, indent=1), encoding="utf-8")
    print(json.dumps({k: v for k, v in q.items() if not k.startswith("топ")}, ensure_ascii=False))
    for k in ("топ корней", "топ групп", "топ правил"):
        print(f"== {k}")
        for x in q[k][:a.топ]:
            print("  " + " | ".join(str(v) for v in x.values()))
    return 0


if __name__ == "__main__":
    sys.exit(main())
