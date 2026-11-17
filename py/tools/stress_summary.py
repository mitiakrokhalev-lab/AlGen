"""Полный учёт плана stress-пилота: успех, остановки, ошибки и отсутствующие.

Успех требует законченного процесса, штатной сводки, CRC/хэша всего raw report
и согласованных kept/folded ID. Пик одного процесса не является пиком cgroup.
"""

import argparse
from collections import Counter
import gzip
import hashlib
import json
import math
from pathlib import Path
import re
import zlib


def read(path):
    result = json.loads(Path(path).read_text(encoding="utf-8"))
    if not isinstance(result, dict):
        raise ValueError("ожидался JSON-объект: " + str(path))
    return result


def inspect_case(folder, case, plan):
    sid = case["id"]
    result = dict(id=sid, baseline=case.get("baseline"), outcome="missing")
    if not (folder / "measurement.json").is_file():
        return result
    try:
        m = result["measurement"] = read(folder / "measurement.json")
        if m.get("scheme") != sid or m.get("scope") != "full native scheme":
            raise ValueError("другой процесс/область измерения")
        if m.get("limits") != {"seconds": plan["seconds_per_process"], "rss_gib": plan["rss_gib"]}:
            raise ValueError("лимиты измерения не совпали с планом")
        result["measurement_matches_plan"] = True
        if m.get("complete") is not True:
            result.update(outcome="incomplete", reason=f"{m.get('stop_reason')}; exit={m.get('returncode')}; scheme={m.get('scheme_status')}")
            return result
        if not all(measured(m.get(k)) for k in ("wall_seconds", "cpu_seconds", "peak_rss_kib")):
            raise ValueError("нет обязательных замеров времени/памяти")
        if m["wall_seconds"] > plan["seconds_per_process"] + 1 or m["peak_rss_kib"] > plan["rss_gib"] * 1024**2:
            result.update(outcome="incomplete", reason="фактический бюджет времени/RSS превышен")
            return result
        if m.get("returncode") != 0 or m.get("stop_reason") != "exited" or m.get("scheme_status") != "ok":
            raise ValueError("complete противоречит завершению процесса")
        summary = read(folder / "results" / (sid + ".json"))
        if (summary.get("id") != sid or summary.get("статус") != "ok"
                or summary.get("условие") != "∀ G : Grp"
                or summary.get("строк противоречат базе") != 0
                or summary.get("посылок") != plan["k"]
                or summary.get("термы") != case["terms"]
                or summary.get("отпечаток") != plan["native_fingerprint"] + ":" + str(plan["k"])):
            raise ValueError("неуспешная сводка, другая библиотека или противоречащие строки")
        stages = [json.loads(s) for s in (folder / "stages.jsonl").read_text().splitlines() if s.strip()]
        engine = next((s.get("engine") for s in reversed(stages) if s.get("stage") == "enumeration:engine"), None)
        result["enumeration_engine"] = engine
        if plan.get("compiled_backend_required") and (
                not isinstance(engine, str) or not re.fullmatch(r"cpp:[0-9a-f]{24}", engine)):
            raise ValueError("скомпилированный backend не подтверждён этапами процесса")
        end = next((s for s in reversed(stages) if s.get("stage") == "run:end"), None)
        if end is None or m.get("saved_report") is not True:
            raise ValueError("нет полного raw report/квитанции E.run")
        h, rows, raw, unknown = hashlib.sha256(), 0, Counter(), set()
        raw_kept, raw_folded, raw_deps, ordinary_sources = set(), set(), {}, set()
        with gzip.open(folder / "report.jsonl.gz", "rb") as f:
            for line in f:
                h.update(line)
                r = json.loads(line)
                verdict = r["вердикт"]
                if verdict.startswith("ОШИБКА") or r.get("ОШИБКА сжатия"):
                    raise ValueError("ошибка вердикта/сжатия в полном report")
                rows += 1
                raw[verdict] += 1
                if verdict == "неизвестно":
                    qid = r["№"]
                    unknown.add(qid)
                    if r.get("свёрнута"):
                        raw_folded.add(qid)
                        deps = r.get("следует из")
                        if not isinstance(deps, list) or not deps or any(not isinstance(d, str) or not d for d in deps):
                            raise ValueError("нет корректных источников raw-свёртки")
                        if any(d.startswith("экземпляр: ") for d in deps):
                            inst = r.get("экземпляр")
                            if (len(deps) != 1 or not deps[0][len("экземпляр: "):].strip()
                                    or not isinstance(inst, dict)
                                    or any(not isinstance(inst.get(k), str) or not inst[k].strip()
                                           for k in ("терм", "вместо"))):
                                raise ValueError("ссылка на экземпляр без метаданных")
                        else:
                            ordinary_sources.update(deps)
                        if qid in raw_deps and raw_deps[qid] != deps:
                            raise ValueError("разные источники raw-свёртки одного №")
                        raw_deps[qid] = deps
                    else:
                        raw_kept.add(qid)
        if rows != end.get("report_rows") or h.hexdigest() != end.get("report_sha256"):
            raise ValueError("число строк/хэш report не совпали")
        if case.get("known_report_sha256") and h.hexdigest() != case["known_report_sha256"]:
            raise ValueError("контрольный report изменился относительно известного эталона")
        if not ordinary_sources <= raw_kept:
            raise ValueError("источник свёртки отсутствует среди оставленных raw-вопросов")
        kept = {r["№"] for r in summary.get("оставленные вопросы", [])}
        folded = set(summary.get("свёрнуто", {}))
        if (kept & folded or unknown != kept | folded or kept != raw_kept or folded != raw_folded
                or summary.get("свёрнуто", {}) != raw_deps):
            raise ValueError("kept/folded/источники не совпали с полным raw report")
        result.update(outcome="ok", report_rows=rows, report_sha256=h.hexdigest(),
                      raw_verdicts=dict(raw), first_class_verdicts=summary.get("вердикты"),
                      unknown_ids=len(unknown), kept_ids=len(kept), folded_ids=len(folded))
    except (OSError, ValueError, TypeError, KeyError, AttributeError, EOFError, zlib.error) as e:
        result.update(outcome="invalid", reason=str(e))
    return result


def measured(value):
    return type(value) in (int, float) and math.isfinite(value) and value >= 0


def collect(plan, root):
    ids = [c["id"] for c in plan["cases"]]
    if not ids or len(ids) != len(set(ids)) or any(not re.fullmatch(r"G(?:-\d+)+", sid) for sid in ids):
        raise ValueError("неверные/повторные ID в плане")
    cases = [inspect_case(Path(root) / c["id"], c, plan) for c in plan["cases"]]
    metrics = {}
    for field in ("wall_seconds", "cpu_seconds", "peak_rss_kib"):
        values = [c.get("measurement", {}).get(field) for c in cases if c.get("measurement_matches_plan")]
        known = [v for v in values if measured(v)]
        metrics[field] = dict(observed=len(known), value=(max(known) if field == "peak_rss_kib" else sum(known)) if known else None)
    ok = [c for c in cases if c["outcome"] == "ok"]
    unknown, kept = sum(c["unknown_ids"] for c in ok), sum(c["kept_ids"] for c in ok)
    return dict(version=1, name=plan["name"], scope=plan["scope"], planned=len(ids),
                outcomes=dict(Counter(c["outcome"] for c in cases)), all_complete=len(ok) == len(ids),
                measurements_all_observed=metrics, unknown_ids_ok=unknown, kept_ids_ok=kept,
                within_scheme_ratio_ok=unknown / kept if kept else None,
                cases=cases, notes=["Сумма wall процессов не wall workflow; неизвестные времена не нули.",
                                   "RSS — пик отдельного процесса, не дерева/cgroup.",
                                   "Выдача посчитана только для проверенных ok; охват — ровно схемы плана.",
                                   "Baseline 16б использовал кэш вердиктов и считал scheme_seconds без startup; новый wall включает startup без прежнего кэша. Прямого коэффициента ускорения нет.",
                                   "Проверяются целостность и согласованность свёрток, а не новое SAT-доказательство базиса."])


def markdown(d):
    rows = ["# " + d["name"], "", f"План: {d['planned']}; итоги: {d['outcomes']}.", "",
            "| Схема | Итог | Wall, с | CPU, с | Пик RSS, GiB | Kept № |", "|---|---|---:|---:|---:|---:|"]
    for c in d["cases"]:
        m = c.get("measurement", {})
        def number(key, scale=1):
            v = m.get(key)
            return f"{v/scale:.3f}" if measured(v) else "—"
        rows.append(f"| {c['id']} | {c['outcome']} | {number('wall_seconds')} | {number('cpu_seconds')} | "
                    f"{number('peak_rss_kib', 1024**2)} | {c.get('kept_ids', '—')} |")
    return "\n".join(rows + ["", *d["notes"]]) + "\n"


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("plan")
    p.add_argument("root")
    p.add_argument("--out", required=True)
    p.add_argument("--markdown")
    p.add_argument("--require-complete", action="store_true")
    a = p.parse_args()
    d = collect(read(a.plan), a.root)
    Path(a.out).write_text(json.dumps(d, ensure_ascii=False, indent=2)+"\n", encoding="utf-8")
    if a.markdown:
        Path(a.markdown).write_text(markdown(d), encoding="utf-8")
    if a.require_complete and not d["all_complete"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
