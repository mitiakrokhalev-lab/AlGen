"""Воспроизводимые локальные SAT-пробы замороженной выборки, без Library build.

Это не повтор native E.run и не доказательство охвата всего класса.
Частичные переводы не считаются закрытием полной задачи.
"""

import argparse
import hashlib
import json
import signal
import time
from pathlib import Path

from algen.etalon import Unsupported, scheme
from algen.logic import App, Theory, Vocab, decide
from algen import table


def run(probes, seconds=20):
    v = Vocab.section("grp")
    universes = {}
    for p in probes:
        start = time.monotonic()
        out = dict(p)
        def expired(*_):
            raise TimeoutError("лимит локальной пробы")
        old_handler = signal.signal(signal.SIGALRM, expired)
        signal.alarm(seconds)
        try:
            g, prem, goal = scheme(v, {**p, "раздел": "grp"})
            # Проверка сорта: сам parser допускает слишком общий литерал.
            for atom, _ in prem + [goal]:
                if atom[0] == "p" and not v.prop_fits(atom[1], g.terms[atom[2]].sort):
                    raise Unsupported("свойство не подходит сорту: " + str(atom))
            initial = set(g.terms)
            tops = table.maximal(g, initial)
            nodes = set().union(*(table.app_nodes(t) for t in tops))
            needed = {str(t) for t in initial if isinstance(t, App) and table.app_nodes(t)}
            out.update(parse="ok", objects=len(initial), premises=len(prem),
                       constructions=len(nodes), terms=sorted(needed), structural_status="not_checked")
            T = Theory(g, grow=1, extra=[a for a, _ in prem + [goal] if a[0] == "r"])
            verdict = decide(T, prem, goal)
            out.update(local_verdict=verdict.kind,
                       core=[(str(a), val) for a, val in verdict.core or []],
                       clauses=len(T.clauses), native_pipeline="not_run")
            if len(nodes) > 2 or len(prem) > 3:
                out["structural_status"] = "translation_exceeds_class"
            else:
                if needed and p["base"] not in universes:
                    universes[p["base"]] = set(table.universe(v, p["base"]))
                missing = sorted(needed - universes.get(p["base"], set()))
                out.update(universe_missing=missing, structural_terms_available=not missing,
                           structural_status="terms_missing" if missing else "terms_available")
        except Unsupported as e:
            out.update(parse="unsupported", reason=str(e), native_pipeline="not_run")
        except TimeoutError as e:
            out.update(reason=str(e), structural_status="not_finished", native_pipeline="not_run")
        finally:
            signal.alarm(0)
            signal.signal(signal.SIGALRM, old_handler)
        out["wall_seconds"] = round(time.monotonic() - start, 6)
        yield out


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("formulas")
    p.add_argument("--out", required=True)
    a = p.parse_args()
    source = Path(a.formulas)
    document = json.loads(source.read_text())
    if table.SIZE != 2:
        p.error("нужно ALGEN_SIZE=2")
    result = dict(version=1, scope="local grow=1 SAT; structural universe check; no native enumeration",
                  source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(), probes=[])
    for row in run(document["probes"]):
        result["probes"].append(row)
        Path(a.out).write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n")
        print(row["id"], row.get("parse"), row.get("local_verdict", row.get("reason")), flush=True)


if __name__ == "__main__":
    main()
