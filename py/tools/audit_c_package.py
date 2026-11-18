"""Audit a proposed rule package on the fixed, complete Table06 G-4-17 result."""

from collections import Counter
import hashlib
import json
import os
from pathlib import Path
import pickle
import resource
import subprocess
import sys
import tempfile
import time
from unittest.mock import patch


SCHEME = "G-4-17-767-769-770-771"
FINGERPRINT = "a32525981b40d3d8:G::s2:быстро"
EXPECTED_REPORT = "6e6584cb31823d1a4be2924547d224f0dd80ef22ffa31fd44c9fe6aa5e301952"
SOURCE_RUN = 44027003918
PACKAGE = Path("../docs/experiments/candidate-batch-G417.json")


def sha(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def write(path, obj):
    path.write_text(json.dumps(obj, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def report_hash(report):
    h = hashlib.sha256()
    for row in report:
        h.update(json.dumps(row, ensure_ascii=False, sort_keys=True, separators=(",", ":")).encode())
        h.update(b"\n")
    return h.hexdigest()


def audit_rows(form, vocabularies, rules):
    """Check every projected Library row against each of the two scoped theories."""
    import numpy as np
    from algen import enumerate as E, table
    from algen.logic import Var

    actual = np.asarray(form.m)
    assert actual.dtype == np.bool_ and actual.shape == (32183, 396)
    assert not (actual[:, ::2] & actual[:, 1::2]).any()
    packed = np.packbits(actual, axis=1, bitorder="little")
    _, indices, multiplicities = np.unique(packed, axis=0, return_index=True, return_counts=True)
    selected = [np.flatnonzero(actual[i]) for i in indices]
    terms = [str(term) for term in form.own if not isinstance(term, Var)]
    domains = {}
    inconsistent = []
    for label, vocab in vocabularies:
        scoped = E.SchemeForm(form.lib, vocab, table.BASES["G"], terms=terms, with_rows=False,
                              grow_ops=table.grow_ops(vocab))
        assert set(form.atoms) <= set(scoped.atoms), "row atoms differ from the scoped graph"
        T, s = scoped.sc.T, scoped.sc.s
        try:
            mapping = [T.lit(atom, sign) for atom in form.atoms for sign in (True, False)]
            bad = set()
            for i, cols in enumerate(selected):
                lits = [mapping[j] for j in cols]
                if any(x is False for x in lits) or not s.solve(assumptions=[x for x in lits if x is not None]):
                    bad.add(i)
            domains[label] = {
                "clauses": len(T.clauses), "inconsistent_projections": len(bad),
                "inconsistent_rows": sum(int(multiplicities[i]) for i in bad),
                "grounded_package_clauses": dict(Counter(x for x in T.origin if x in rules)),
            }
            inconsistent.append(bad)
        finally:
            s.delete()
    newly_bad = inconsistent[1] - inconsistent[0]
    return {"rows": len(actual), "source_columns": actual.shape[1], "distinct_projections": len(selected),
            "theories": domains, "newly_inconsistent_rows": sum(int(multiplicities[i]) for i in newly_bad),
            "scope": "All rows of the G-4-17 Library projection; joint consistency in the scoped theory."}


def propagate_in_projection(form, report, package):
    """Apply proved implications to known row bits, then find exact contrary witnesses."""
    import numpy as np
    from algen import enumerate as E

    if form.fixed_lits or not E.CLOSE_MARKED:
        raise ValueError("Expected the fixed Table06 scheme and its all-facts matrix")
    by_name = {E.lit_name(atom, sign): 2 * i + offset
               for i, atom in enumerate(form.atoms) for offset, sign in enumerate((True, False))}
    assert len(by_name) == 2 * len(form.atoms)
    roots = [str(term) for term in form.own if form.g.terms[term].sort == "Grp.obj"]
    initial = np.asarray(form.m)
    matrix = initial.copy()

    def literal_name(lit, root):
        term = lit["t"]
        if term == "X":
            name = root
        elif term == {"op": "aut", "args": ["X"]}:
            name = f"aut({root})"
        else:
            raise ValueError("Unexpected term in audited package")
        sign = "" if lit.get("значение", True) else "¬"
        return f"{sign}{lit['p']}({name})"

    instances = []
    missing = Counter()
    updates = Counter()
    for rule in package["добавить"]:
        for root in roots:
            names = [literal_name(lit, root) for lit in [*rule["if"], rule["then"]]]
            if any(name not in by_name for name in names):
                missing[rule["id"]] += 1
                continue
            *premises, goal = [by_name[name] for name in names]
            instances.append((rule["id"], premises, goal))
    while True:
        added = 0
        for name, premises, goal in instances:
            match = matrix[:, premises].all(axis=1)
            if (match & matrix[:, goal ^ 1]).any():
                raise ValueError("Proposed rule conflicts with a known value in the projection")
            fill = match & ~matrix[:, goal]
            count = int(fill.sum())
            matrix[fill, goal] = True
            updates[name] += count
            added += count
        if not added:
            break
    changed = set(np.flatnonzero((matrix != initial).any(axis=0)).tolist())
    old = np.packbits(initial.T, axis=1)
    new = np.packbits(matrix.T, axis=1)
    refuted, kept, id_kinds = set(), set(), {}
    for row in report:
        if row["вердикт"] != "неизвестно":
            continue
        qid = row["№"]
        cols = [by_name[name] for name in row["запрет"]]
        if not row.get("свёрнута"):
            kept.add(qid)
            id_kinds.setdefault(qid, row["вид"])
        if not changed.intersection(cols):
            continue
        if np.bitwise_and.reduce(old[cols], axis=0).any():
            raise ValueError("A baseline unknown is already refuted on the original input")
        if np.bitwise_and.reduce(new[cols], axis=0).any():
            refuted.add(qid)
    return {
        "known_cells_added": int((matrix != initial).sum()), "updates_by_rule": dict(updates),
        "grounded_instances_in_projection": len(instances), "missing_instance_columns": dict(missing),
        "previous_unknown_IDs_refuted": len(refuted),
        "previous_kept_unknown_IDs_refuted": len(refuted & kept),
        "previous_kept_kind_counts_refuted": dict(Counter(id_kinds[q] for q in refuted & kept)),
        "scope": "Direct rule propagation and real row witnesses for fixed old report variants. No fresh minima, basis or verdict pipeline.",
    }


def child(output, receipt):
    from algen import enumerate as E, library, table
    from algen.logic import Vocab
    sys.path.insert(0, str(Path("tests").resolve()))
    from test_rules_C_questions import kind

    t = time.perf_counter()
    proposed = json.loads(PACKAGE.read_text())
    rules = {r["id"] for r in proposed["добавить"]}
    before, after = Vocab.section("grp"), Vocab.section("grp")
    if rules.intersection(r["id"] for r in before.rules):
        raise ValueError("Duplicate rule ID")
    after.apply(proposed)
    if table._fp("G") != FINGERPRINT:
        raise ValueError("Table06 fingerprint mismatch")
    cache = Path("../кэш") / f"библиотека-{library._fingerprint()}.pickle"
    def cached(_vocab):
        with cache.open("rb") as stream:
            return pickle.load(stream)
    table.built_library = cached
    run = E.run
    def audited(*args, **kwargs):
        receipt["phase"] = "baseline_generation"
        result = run(*args, **kwargs)
        receipt["phase"] = "baseline_report_check"
        form, alive, _, report = result
        expected = report_hash(report)
        receipt["baseline_report_sha256"] = expected
        if expected != EXPECTED_REPORT:
            raise ValueError("Baseline report hash differs from confirmed Table06 control")
        summary = form.knowledge["сводка"]
        counts = summary["оставленные после сжатия"]
        cases = summary["вопросы человеку"]
        assert len(cases) == counts["вопросов человеку (C)"] == 3
        assert len(report) == len(alive) == 20823
        receipt.update(baseline_report_sha256=expected, baseline_report_rows=len(report),
                       kept_unknowns=counts["запретов"], current_c_count=len(cases),
                       kept_AB=counts["ждут знаний (A + B)"],
                       kept_roots=counts["корней знаний всего"])
        vocabularies = [("before", before), ("after", after)]
        receipt["phase"] = "scoped_C_verdicts"
        receipt["current_C_verdicts"] = []
        for item in cases:
            r = {"ID": item["№"]}
            for label, vocab in vocabularies:
                with patch.object(Vocab, "section", return_value=vocab):
                    r[label] = kind(item["запрет"])
            receipt["current_C_verdicts"].append(r)
        receipt["newly_proved_on_fixed_C"] = sum(
            r["before"] == "неизвестно" and r["after"] == "выводится" for r in receipt["current_C_verdicts"])
        try:
            receipt["phase"] = "library_vs_scoped_theory"
            receipt["library_row_audit"] = audit_rows(form, vocabularies, rules)
            receipt["phase"] = "direct_value_propagation"
            receipt["direct_value_control"] = propagate_in_projection(form, report, proposed)
        except Exception as exc:
            receipt["library_row_audit_error"] = type(exc).__name__
            raise
        receipt["phase"] = "rendering"
        return result
    E.run = audited
    sys.argv = ["table", "перебор", "G", "--каталог", "../native-tabs", "--выход", str(output.parent),
                "--нитей", "1", "--посылок", "3", "--схемы", SCHEME, "--предел", "1150"]
    receipt["phase"] = "table_setup"
    table.main()
    summary = output.parent / (SCHEME + ".json")
    usage = resource.getrusage(resource.RUSAGE_SELF)
    receipt.update(source_run=SOURCE_RUN, table_fingerprint=FINGERPRINT, scheme=SCHEME,
                   proposed_rules_sha256=sha(PACKAGE),
                   code_checkout=subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip(),
                   wall_seconds=time.perf_counter() - t, cpu_seconds=usage.ru_utime + usage.ru_stime,
                   peak_rss_kib=usage.ru_maxrss, filesystem_input_blocks=usage.ru_inblock,
                   filesystem_output_blocks=usage.ru_oublock)
    receipt["generator_status"] = json.loads(summary.read_text()).get("статус") if summary.is_file() else None
    audit = receipt.get("library_row_audit", {})
    receipt["complete"] = (receipt["generator_status"] == "ok" and bool(audit)
                           and not audit["newly_inconsistent_rows"]
                           and all(not item["inconsistent_rows"] for item in audit["theories"].values())
                           and set(audit["theories"]["after"]["grounded_package_clauses"]) == rules
                           and "direct_value_control" in receipt)
    if receipt["complete"]:
        receipt["phase"] = "complete"
    write(output, receipt)
    return 0 if receipt["complete"] else 1


def main():
    if len(sys.argv) == 3 and sys.argv[1] == "--child":
        output = Path(sys.argv[2])
        receipt = {"phase": "startup"}
        try:
            return child(output, receipt)
        except Exception as exc:
            receipt.update(error_class=type(exc).__name__, complete=False)
            write(output, receipt)
            return 1
    env = {k: v for k, v in os.environ.items() if not k.startswith("ALGEN_")}
    env.update(ALGEN_SIZE="2", ALGEN_FAST="1", ALGEN_COMPRESS="1", ALGEN_NATIVE_GROUP_ROWS="1",
               ALGEN_KNOWLEDGE="1", ALGEN_SKEL=str(Path("../native/skel").resolve()),
               PYTHONHASHSEED="1", OPENBLAS_NUM_THREADS="1", OMP_NUM_THREADS="1")
    scratch = Path(tempfile.mkdtemp(prefix="algen-c-audit-"))
    t = time.perf_counter()
    reason, sampled_rss = "exited", 0
    with (scratch / "process.log").open("w", encoding="utf-8") as log:
        proc = subprocess.Popen([sys.executable, "-B", "-m", "tools.audit_c_package", "--child", str(scratch / "result.json")],
                                env=env, stdout=log, stderr=subprocess.STDOUT)
        try:
            while proc.poll() is None:
                try:
                    status = Path(f"/proc/{proc.pid}/status").read_text()
                    rss = next((int(line.split()[1]) for line in status.splitlines() if line.startswith("VmRSS:")), 0)
                    sampled_rss = max(sampled_rss, rss)
                except FileNotFoundError:
                    pass
                if sampled_rss > 14 * 1024**2 or time.perf_counter() - t > 1250:
                    reason = "rss_budget" if sampled_rss > 14 * 1024**2 else "time_budget"
                    break
                time.sleep(0.25)
        finally:
            if proc.poll() is None:
                proc.terminate()
                try:
                    proc.wait(timeout=5)
                except subprocess.TimeoutExpired:
                    proc.kill()
                    proc.wait()
    rc = proc.returncode
    result = scratch / "result.json"
    receipt = json.loads(result.read_text()) if result.is_file() else {}
    receipt.update(returncode=rc, stop=reason, process_wall_seconds=time.perf_counter() - t,
                   sampled_peak_rss_kib=sampled_rss, limits={"seconds": 1250, "sampled_rss_gib": 14},
                   process_log_sha256=sha(scratch / "process.log"))
    receipt["complete"] = receipt.get("complete", False) and rc == 0 and reason == "exited"
    write(Path("../tool-out/c-package-audit.json"), receipt)
    print(json.dumps({"complete": receipt["complete"], "returncode": rc, "stop": reason}, ensure_ascii=False))
    return 0 if receipt["complete"] else 1


if __name__ == "__main__":
    sys.exit(main())
