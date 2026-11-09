"""Воспроизводимые метрики пилота, включая ошибки и незавершённые схемы.

Историческое поле «память ГБ» — Linux VmRSS KiB / 1e6, а не GiB и не пик.
Сумма времён схем не является CPU-time или временем параллельного workflow.
"""

import argparse
from collections import Counter
import json
import math
from pathlib import Path
import statistics


def measured(x):
    return type(x) in (int, float) and math.isfinite(x)


def distribution(values):
    xs = sorted(x for x in values if measured(x))
    return ({"n": len(xs), "sum": round(sum(xs), 3), "median": statistics.median(xs),
             "p95": xs[math.ceil(.95 * len(xs)) - 1], "max": xs[-1]} if xs else {"n": 0})


def collect(directory):
    directory = Path(directory)
    plans = sorted(directory.glob("_план-*.json"))
    planned = set()
    for p in plans:
        planned.update(json.loads(p.read_text(encoding="utf-8"))["схемы"])
    rows = {}
    paths = {}
    for p in sorted(directory.glob("*.json")):
        d = json.loads(p.read_text(encoding="utf-8"))
        if not isinstance(d, dict) or "id" not in d or "статус" not in d:
            continue
        if d["id"] in rows:
            raise ValueError("дублирующийся результат схемы: " + d["id"])
        rows[d["id"]] = {k: d.get(k) for k in ("статус", "секунд", "память ГБ", "вердикты")}
        rows[d["id"]].update(kept_count=len(d.get("оставленные вопросы", [])),
                              has_compression="оставленные вопросы" in d)
        kq, fq = d.get("оставленные вопросы"), d.get("свёрнуто")
        ids = None
        if isinstance(kq, list) and isinstance(fq, dict) and all(isinstance(q, dict) and q.get("№") for q in kq):
            ks, fs = {q["№"] for q in kq}, set(fq)
            ids = (len(ks | fs), len(ks), len(fs), len(ks & fs))
        elif d.get("вердикты") == {}:
            ids = (0, 0, 0, 0)
        rows[d["id"]]["compression_ids"] = ids
        paths[d["id"]] = p
    ok = [d for d in rows.values() if d["статус"] == "ok"]
    oom, unclassified = [], []
    for sid, d in rows.items():
        if d["статус"] == "ошибка: память":
            oom.append(sid)
        elif d["статус"].startswith("ошибка"):
            log = paths[sid].with_suffix(".txt")
            memory = False
            if log.is_file():
                with log.open(encoding="utf-8") as f:
                    memory = any("MemoryError" in line for line in f)
            if memory:
                oom.append(sid)
            else:
                unclassified.append(sid)
    verdicts = sum((Counter(d["вердикты"]) for d in ok if isinstance(d["вердикты"], dict)), Counter())
    kept = sum(d["kept_count"] for d in ok)
    unknown = verdicts.get("неизвестно", 0)
    missing_ids = sorted(sid for sid, d in rows.items() if d["статус"] == "ok" and d["compression_ids"] is None)
    overlap_ids = sorted(sid for sid, d in rows.items() if d["статус"] == "ok" and
                         d["compression_ids"] is not None and d["compression_ids"][3])
    sums = [sum(d["compression_ids"][i] for d in ok if d["compression_ids"] is not None) for i in range(3)]
    return {"version": 2, "planned": len(planned) if plans else None, "reported": len(rows),
            "statuses": dict(Counter(d["статус"] for d in rows.values())),
            "missing": sorted(planned - rows.keys()) if plans else None,
            "unexpected": sorted(rows.keys() - planned) if plans else None,
            "oom_confirmed": len(oom), "errors_unclassified": unclassified,
            "time_seconds_all_observed": distribution(d.get("секунд") for d in rows.values()),
            "time_seconds_ok_only": distribution(d.get("секунд") for d in ok),
            "time_unreported": sorted(sid for sid, d in rows.items() if not measured(d.get("секунд"))),
            "ok_missing_verdicts": sorted(sid for sid, d in rows.items() if d["статус"] == "ok" and not isinstance(d["вердикты"], dict)),
            "verdict_classes_ok": dict(verdicts), "kept_within_schemes": kept,
            "unknown_ids_before_compression": sums[0] if not missing_ids else None,
            "kept_ids_within_schemes": sums[1] if not missing_ids else None,
            "folded_ids_within_schemes": sums[2] if not missing_ids else None,
            "compression_accounting_incomplete": missing_ids,
            "compression_id_overlaps": overlap_ids,
            "summary_counter_ratio": unknown / kept if kept else None,
            "within_scheme_ratio": sums[0] / sums[1] if sums[1] and not missing_ids and not overlap_ids
                and all(isinstance(d["вердикты"], dict) for d in ok) else None,
            "compression_reports": sum(d["has_compression"] for d in ok),
            "zero_unknown_without_compression_report": sum(not d["has_compression"] and isinstance(d["вердикты"], dict) and
                not d["вердикты"].get("неизвестно", 0) for d in ok),
            "rss_observations_historical_units": distribution(x for d in rows.values() for x in (d.get("память ГБ") or [])),
            "peak_rss_gib": None, "cpu_seconds": None, "workflow_wall_seconds": None,
            "global_verified_basis": None,
            "notes": ["Сумма секунд схем не CPU-time и не wall workflow; отсутствующие времена не равны нулю.",
                      "RSS: Linux KiB / 1e6, две точки на схему; peak неизвестен.",
                      "Вердикты — первый вердикт класса, сжатие — все неизвестные строки по №; это разные правила учёта.",
                      "within_scheme_ratio использует объединение kept/folded №, summary_counter_ratio — лишь отношение старых счётчиков.",
                      "Общая полнота при ошибках не достигнута."]}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("directory")
    p.add_argument("--out")
    p.add_argument("--source", help="URL исходного запуска")
    p.add_argument("--workflow-wall", type=float, help="наблюдённое wall workflow из timestamps, не CPU")
    a = p.parse_args()
    result = collect(a.directory)
    result.update(source=a.source, workflow_wall_seconds=a.workflow_wall)
    text = json.dumps(result, ensure_ascii=False, indent=2) + "\n"
    if a.out:
        Path(a.out).write_text(text, encoding="utf-8")
    else:
        print(text, end="")


if __name__ == "__main__":
    main()
