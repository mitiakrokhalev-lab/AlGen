"""Сводка переписи объёма (ALGEN_CENSUS=1): сколько минимальных условий даёт
каждая схема, сколько времени и памяти стоит перебор до вердиктов.

python3 -B -m tools.census_summary <каталог json схем> --plan <_план-*.json ...> --out census.json
Каждая схема плана учитывается: перепись / таймаут / ошибка / нет результата.
"""
import argparse
import json
from pathlib import Path


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("dir")
    p.add_argument("--out", required=True)
    p.add_argument("--parts", type=int, required=True, help="число частей: план каждой обязателен")
    p.add_argument("--expect", type=int, default=0, help="ожидаемое число схем базы (0 — не сверять)")
    a = p.parse_args()
    root = Path(a.dir)
    planned, missing_parts = [], []
    for i in range(1, a.parts + 1):
        files = list(root.rglob(f"_план-{i}-{a.parts}.json"))
        if not files:
            missing_parts.append(i)
            continue
        planned += json.loads(files[0].read_text(encoding="utf-8"))["схемы"]
    recs = {}
    for f in root.rglob("*.json"):
        if f.name.startswith("_"):
            continue
        try:
            r = json.loads(f.read_text(encoding="utf-8"))
        except Exception:
            continue
        if isinstance(r, dict) and "id" in r and "статус" in r:
            recs[r["id"]] = r
    rows, outcomes = [], {}
    for sid in planned:
        r = recs.get(sid)
        status = "нет результата" if r is None else r["статус"]
        outcomes[status] = outcomes.get(status, 0) + 1
        c = (r or {}).get("перепись") or {}
        mem = (r or {}).get("память ГБ") or [None, None]
        stages = (r or {}).get("память по этапам") or []
        rows.append(dict(id=sid, статус=status, секунд=(r or {}).get("секунд"),
                         минимальных=c.get("минимальных"), не_опровергнуто=c.get("не опровергнуто"),
                         пустых=c.get("пустых посылок"), по_длине=c.get("по длине"),
                         rss_конец=mem[-1], rss_этапы=[s[1] for s in stages]))
    done = [r for r in rows if r["минимальных"] is not None]
    mins = sorted(r["минимальных"] for r in done)
    def q(x):
        return mins[min(len(mins) - 1, int(x * len(mins)))] if mins else None
    summary = dict(схем_в_плане=len(planned), частей_без_плана=missing_parts,
                   ожидалось_схем=a.expect or None,
                   полный_план=(not missing_parts and (not a.expect or len(planned) == a.expect)),
                   исходы=outcomes, посчитано=len(done),
                   минимальных_всего=sum(mins), медиана=q(.5), p90=q(.9), p99=q(.99),
                   максимум=mins[-1] if mins else None,
                   секунд_всего=round(sum(r["секунд"] or 0 for r in rows), 1),
                   крупнейшие=sorted(done, key=lambda r: -r["минимальных"])[:30])
    Path(a.out).write_text(json.dumps(dict(сводка=summary, схемы=rows), ensure_ascii=False, indent=1),
                           encoding="utf-8")
    print(json.dumps({k: v for k, v in summary.items() if k != "крупнейшие"}, ensure_ascii=False, indent=1))
    if not summary["полный_план"]:
        print("ВНИМАНИЕ: план переписи неполный (части без плана или число схем не совпало)")
    for r in summary["крупнейшие"]:
        print(r["id"], r["минимальных"], r["секунд"], r["rss_конец"])


if __name__ == "__main__":
    main()
