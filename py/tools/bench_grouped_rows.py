"""Compare two full calculations on one runner; publish only counts and hashes."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import resource
import subprocess
import sys
import tempfile
import time
from functools import wraps


def sha(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def canonical(value):
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":")).encode()


def inputs(a):
    paths = (sorted(Path(a.tables).glob("G*.pickle"))
             + sorted(Path(a.skel).glob("G*.pickle"))
             + sorted(Path(a.library_cache).glob("библиотека-*.pickle")))
    if not paths:
        raise ValueError("No input files")
    return {str(p.resolve()): {"bytes": p.stat().st_size, "sha256": sha(p)} for p in paths}


def usage():
    r = resource.getrusage(resource.RUSAGE_SELF)
    return dict(cpu_seconds=r.ru_utime + r.ru_stime, peak_rss_kib=r.ru_maxrss,
                filesystem_input_blocks=r.ru_inblock, filesystem_output_blocks=r.ru_oublock)


def json_file(path, data):
    path.write_text(json.dumps(data, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def child(a):
    import pickle
    from algen import enumerate as E, library, native_enum as N, table

    start = time.perf_counter()
    output = Path(a.scratch)
    receipt = {}
    # The prepared cache is an input. Never rebuild it or delete another cache.
    lib_path = Path(a.library_cache) / f"библиотека-{library._fingerprint()}.pickle"
    def read_library(_vocab):
        with lib_path.open("rb") as stream:
            return pickle.load(stream)
    table.built_library = read_library
    receipt["table_fingerprint"] = table._fp("G")
    if receipt["table_fingerprint"] != a.fingerprint:
        raise ValueError("Prepared input fingerprint differs from the loaded code and data")

    original_group = N.group_equal_rows
    @wraps(original_group)
    def group(matrix):
        t = time.perf_counter()
        result = original_group(matrix)
        receipt["grouping"] = dict(input=list(matrix.shape),
                                   groups=None if result is None else len(result[0]),
                                   wall_seconds=time.perf_counter() - t)
        return result
    N.group_equal_rows = group

    original_enum = E.enumerate_form
    @wraps(original_enum)
    def enumerate_form(*args, **kwargs):
        t, cpu = time.perf_counter(), time.process_time()
        alive, empty = original_enum(*args, **kwargs)
        form = args[0]
        receipt["enumeration"] = dict(wall_seconds=time.perf_counter() - t,
                                      cpu_seconds=time.process_time() - cpu,
                                      engine=form.enumeration_engine, alive=len(alive), empty=len(empty),
                                      n_alive=form.n_alive, packed_bytes=alive.nbytes + empty.nbytes)
        h = hashlib.sha256()
        t = time.perf_counter()
        for depth, (keys, values) in alive.blocks.items():
            h.update(canonical([depth, len(keys), keys.typecode, values.typecode]))
            h.update(memoryview(keys))
            h.update(memoryview(values))
        h.update(b"empty\n")
        for depth, codes in empty.blocks:
            h.update(canonical([depth, len(codes), codes.typecode]))
            h.update(memoryview(codes))
        receipt["enumeration"]["sha256"] = h.hexdigest()
        receipt["enumeration_digest_seconds"] = time.perf_counter() - t
        return alive, empty
    E.enumerate_form = enumerate_form

    original_run = E.run
    @wraps(original_run)
    def run(*args, **kwargs):
        result = original_run(*args, **kwargs)
        form, alive, empty, report = result
        h = hashlib.sha256()
        count = 0
        t = time.perf_counter()
        for row in report:
            line = canonical(row) + b"\n"
            h.update(line)
            count += len(line)
        receipt["report"] = dict(rows=len(report), bytes=count, sha256=h.hexdigest(),
                                 digest_seconds=time.perf_counter() - t)
        receipt["final_minima"] = len(alive)
        if getattr(form, "census", None) is not None:
            raise ValueError("Full report required")
        return result
    E.run = run

    sys.argv = ["table", "перебор", "G", "--каталог", a.tables, "--выход", str(output),
                "--схемы", a.scheme, "--нитей", "1", "--посылок", "3", "--предел", str(a.seconds)]
    table.main()
    receipt["wall_seconds"] = time.perf_counter() - start
    receipt.update(usage())
    report_path = output / (a.scheme + ".json")
    if report_path.is_file():
        record = json.loads(report_path.read_text())
        receipt["summary"] = {"bytes": report_path.stat().st_size,
                              "status": record.get("статус"),
                              "scheme_seconds": record.get("секунд")}
        for key in ("запретов", "вердикты", "оставленные вопросы", "оставленные факты", "свёрнуто"):
            if key in record:
                value = record[key]
                receipt["summary"][key] = len(value) if isinstance(value, (list, dict)) and key != "вердикты" else value
        for key in ("секунд", "память ГБ", "память по этапам"):
            record.pop(key, None)
        knowledge = record.get("знания", {})
        receipt["knowledge_time"] = knowledge.pop("секунд разметки", None)
        if knowledge:
            receipt["knowledge_counts"] = {
                k: {name: counts.get(name) for name in ("запретов", "вопросов человеку (C)",
                                                        "ждут знаний (A + B)", "корней знаний всего")}
                for k, counts in knowledge.items()
                if k in ("все неизвестные", "оставленные после сжатия")
            }
        receipt["summary"]["sha256_without_timings"] = hashlib.sha256(canonical(record)).hexdigest()
        txt = report_path.with_suffix(".txt")
        receipt["text"] = dict(bytes=txt.stat().st_size, sha256=sha(txt))
    receipt["sources"] = {str(Path(module.__file__).resolve()): sha(Path(module.__file__))
                          for module in (E, library, N, table)}
    native = Path(N.__file__).with_suffix(".cpp")
    receipt["sources"][str(native.resolve())] = sha(native)
    json_file(output / "receipt.json", receipt)


def rss(pid):
    try:
        for line in Path(f"/proc/{pid}/status").read_text().splitlines():
            if line.startswith("VmRSS:"):
                return int(line.split()[1])
    except FileNotFoundError:
        return 0
    return 0


def measure(a, mode, output):
    output.mkdir()
    env = {k: v for k, v in os.environ.items() if not k.startswith("ALGEN_")}
    env.update(ALGEN_SIZE="2", ALGEN_FAST="1", ALGEN_COMPRESS="1", ALGEN_SKEL=a.skel,
               ALGEN_KNOWLEDGE=str(int(a.knowledge)), ALGEN_NATIVE_GROUP_ROWS=mode,
               PYTHONHASHSEED="1", OPENBLAS_NUM_THREADS="1", OMP_NUM_THREADS="1",
               PYTHONPATH=os.pathsep.join(sys.path))
    command = [sys.executable, "-B", str(Path(__file__).resolve()), "--child", "--scratch", str(output),
               "--tables", a.tables, "--skel", a.skel, "--library-cache", a.library_cache,
               "--scheme", a.scheme, "--seconds", str(a.seconds), "--fingerprint", a.fingerprint]
    t = time.perf_counter()
    before = resource.getrusage(resource.RUSAGE_CHILDREN)
    sampled, stop = 0, "exited"
    with (output / "process.log").open("wb") as log:
        proc = subprocess.Popen(command, env=env, stdout=log, stderr=subprocess.STDOUT)
        try:
            while proc.poll() is None:
                sampled = max(sampled, rss(proc.pid))
                if sampled > a.rss_gib * 1024**2 or time.perf_counter() - t > a.seconds:
                    stop = "rss_budget" if sampled > a.rss_gib * 1024**2 else "time_budget"
                    proc.terminate()
                    try:
                        proc.wait(timeout=5)
                    except subprocess.TimeoutExpired:
                        proc.kill()
                        proc.wait()
                    break
                time.sleep(0.25)
        finally:
            if proc.poll() is None:
                proc.kill()
                proc.wait()
    after = resource.getrusage(resource.RUSAGE_CHILDREN)
    receipt_file = output / "receipt.json"
    receipt = json.loads(receipt_file.read_text()) if receipt_file.is_file() else None
    return dict(mode=mode, returncode=proc.returncode, stop=stop,
                wall_seconds=time.perf_counter() - t, sampled_rss_kib=sampled,
                cpu_seconds=after.ru_utime + after.ru_stime - before.ru_utime - before.ru_stime,
                log_sha256=sha(output / "process.log"), receipt=receipt)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--tables", required=True)
    p.add_argument("--skel", required=True)
    p.add_argument("--library-cache", required=True)
    p.add_argument("--scheme", required=True)
    p.add_argument("--source-run", type=int)
    p.add_argument("--fingerprint")
    p.add_argument("--seconds", type=int, default=1200)
    p.add_argument("--rss-gib", type=float, default=14)
    p.add_argument("--knowledge", action="store_true")
    p.add_argument("--output")
    p.add_argument("--scratch")
    p.add_argument("--child", action="store_true")
    a = p.parse_args()
    if a.child:
        child(a)
        return
    if not a.output or a.seconds <= 0 or a.rss_gib <= 0:
        p.error("--output and positive time/memory limits required")
    if a.fingerprint is None:
        caches = sorted(Path(a.library_cache).glob("библиотека-*.pickle"))
        if len(caches) != 1:
            p.error("Specify --fingerprint when the library cache is ambiguous")
        h = caches[0].stem.removeprefix("библиотека-")
        a.fingerprint = f"{h}:G::s2:быстро"
    started = time.perf_counter()
    from algen import native_enum
    if native_enum.library() is None:
        raise RuntimeError(native_enum._unavailable)
    scratch = Path(a.scratch) if a.scratch else Path(tempfile.mkdtemp(prefix="algen-row-pair-"))
    scratch.mkdir(parents=True, exist_ok=True)
    preparation_wall = time.perf_counter() - started
    original = inputs(a)
    results = []
    fingerprints = [original]
    for mode in ("1", "0"):
        results.append(measure(a, mode, scratch / mode))
        fingerprints.append(inputs(a))
    def complete(result):
        r = result["receipt"]
        return (result["returncode"] == 0 and result["stop"] == "exited" and r is not None
                and r.get("summary", {}).get("status") == "ok"
                and r.get("enumeration", {}).get("engine", "").startswith("cpp:")
                and r["report"]["rows"] > 0)
    match = {}
    if all(complete(r) for r in results):
        left, right = (v["receipt"] for v in results)
        match = dict(
            enumeration=left["enumeration"]["sha256"] == right["enumeration"]["sha256"]
                        and left["enumeration"]["n_alive"] == right["enumeration"]["n_alive"],
            report=left["report"]["sha256"] == right["report"]["sha256"],
            summary=left["summary"]["sha256_without_timings"] == right["summary"]["sha256_without_timings"],
            text=left["text"]["sha256"] == right["text"]["sha256"],
            same_code=left["sources"] == right["sources"],
            table=left["table_fingerprint"] == right["table_fingerprint"] == a.fingerprint,
            final_minima=left["final_minima"] == right["final_minima"],
            matrix=left["grouping"]["input"] == right["grouping"]["input"],
            knowledge=all(bool(r.get("knowledge_counts")) == a.knowledge for r in (left, right)),
            actual_grouping=left["grouping"]["groups"] is not None and right["grouping"]["groups"] is None)
    stable = fingerprints[0] == fingerprints[1] == fingerprints[2]
    result = dict(scheme=a.scheme, source_run=a.source_run, expected_fingerprint=a.fingerprint,
                  knowledge=a.knowledge, k=3, size=2, sample=None,
                  interpreter=sys.version, native_source_key=native_enum.library().source_hash,
                  limits={"seconds": a.seconds, "rss_gib": a.rss_gib}, order=["grouped", "ungrouped"],
                  shared_native_setup_wall_seconds=preparation_wall,
                  total_wall_seconds=time.perf_counter() - started,
                  checkout=subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip()
                           if Path("../.git").exists() else None,
                  inputs_before=original, inputs_unchanged=stable, equal=match,
                  modes=results, complete=bool(match) and all(match.values()) and stable)
    if not stable:
        result["inputs_after_grouped"], result["inputs_after_ungrouped"] = fingerprints[1:]
    json_file(Path(a.output), result)
    print(json.dumps({key: result[key] for key in ("scheme", "complete", "equal")}, ensure_ascii=False))
    raise SystemExit(0 if result["complete"] else 1)


if __name__ == "__main__":
    main()
