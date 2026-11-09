"""Одна настоящая схема из готовых таблиц: RSS/peak/CPU и размеры структур.

Ограничение родителя останавливает процесс до исчерпания памяти машины.
Остановка — незавершённый замер, не успешная схема. Ничего не фильтруется.
"""

import argparse
from contextlib import nullcontext
from functools import wraps
import gzip
import hashlib
import json
import os
from pathlib import Path
import resource
import struct
import re
import subprocess
import sys
import time


def rss(pid):
    try:
        return {line.split(":", 1)[0]: int(line.split()[1]) for line in
                Path(f"/proc/{pid}/status").read_text().splitlines()
                if line.startswith(("VmRSS:", "VmHWM:"))}
    except (OSError, ProcessLookupError):
        return {}


def valid_enumeration_receipt(receipt, with_minimal):
    if not isinstance(receipt, dict) or receipt.get("stage") != "enumeration:verified":
        return False
    digest = lambda x: isinstance(x, str) and re.fullmatch(r"[0-9a-f]{64}", x) is not None
    return (all(type(receipt.get(k)) is int and receipt[k] >= 0 for k in ("entries", "empty", "n_alive"))
            and digest(receipt.get("enumeration_sha256"))
            and (not with_minimal or digest(receipt.get("minimal_sha256")))
            and isinstance(receipt.get("engine"), str) and bool(receipt["engine"]))


def child(a):
    from algen import enumerate as E, library, table, fast, logic
    library.CACHE = Path(a.library_cache).resolve()
    out = Path(a.out)
    stream = (out / "stages.jsonl").open("a", encoding="utf-8", buffering=1)
    start = time.monotonic()
    def record(stage, **fields):
        stream.write(json.dumps(dict(stage=stage, seconds=round(time.monotonic()-start, 3),
                                     memory_kib=rss(os.getpid()), **fields), ensure_ascii=False) + "\n")
    def size(x):
        return dict(entries=len(x), container_bytes=sys.getsizeof(x),
                    packed_bytes=getattr(x, "nbytes", None)) if x is not None else None
    class EnumerationComplete(BaseException):
        pass

    def packed_digest(name, form, alive, empty):
        header = dict(literals=alive.literals, max_premises=alive.max_premises,
                      max_support=alive.max_support, n_alive=form.n_alive, empty=len(empty),
                      blocks=[dict(depth=d, count=len(k), keys=k.typecode, supports=v.typecode)
                              for d, (k, v) in alive.blocks.items()])
        h = hashlib.sha256()
        with ((out / (name + ".bin")).open("wb") if a.save_enumeration else nullcontext(None)) as dest:
            def write(data):
                h.update(data)
                if dest is not None:
                    dest.write(data)
            write(json.dumps(header, sort_keys=True, separators=(",", ":")).encode() + b"\n")
            for keys, values in alive.blocks.values():
                write(memoryview(keys)); write(memoryview(values))
            chunk = bytearray()
            for prem in empty:
                code = 1
                for j in prem:
                    code = (code << alive.width) | j
                chunk.extend(struct.pack("<Q", code))
                if len(chunk) >= 65536:
                    write(chunk); chunk.clear()
            if chunk:
                write(chunk)
        return h.hexdigest()
    def search_state(form):
        from algen.deferred import DeferredSolver
        handle = form.search.s
        delayed = isinstance(handle, DeferredSolver)
        return dict(deferred=delayed, materialized=handle.materialized if delayed else True)
    for name in ("built_library", "skeleton", "load"):
        fn = getattr(table, name)
        def setup(*args, _fn=fn, _name=name, **kwargs):
            record(_name + ":start")
            result = _fn(*args, **kwargs)
            record(_name + ":end")
            return result
        setattr(table, name, setup)
    if a.table_only:
        # Изолированный замер storage: реальные части, но без загрузки теории.
        # Он доказывает равенство битов, а не совпадение математических вердиктов.
        import pickle
        from types import SimpleNamespace
        first = next(iter(sorted(Path(a.tables).glob("G.*-*.pickle"))))
        with first.open("rb") as f:
            width = pickle.load(f)["атомов"]
        table.skeleton = lambda *args: SimpleNamespace(atoms=[None] * width)
        form = table.load(None, None, "G", a.tables)
        hashes = {}
        for name in "mse":
            matrix = getattr(form, name)
            hashes[name] = hashlib.sha256(matrix.bits).hexdigest()
        record("table:verified", shape=list(form.m.shape), bit_sha256=hashes,
               assignments_sha256=hashlib.sha256(json.dumps(
                   [{str(k): v for k, v in env.items()} for env in form.envs],
                   sort_keys=True, ensure_ascii=False).encode()).hexdigest(),
               skipped=len(form.skipped))
        return
    solver = logic.Theory.solver
    solver_count = 0
    def make_solver(theory):
        nonlocal solver_count
        solver_count += 1
        number = solver_count
        record("solver:start", number=number, clauses=len(theory.clauses))
        result = solver(theory)
        record("solver:end", number=number)
        return result
    logic.Theory.solver = make_solver
    if a.load_only:
        lib = table.built_library(table.Vocab.section("grp"))
        form = table.load(lib, table.Vocab.section("grp"), "G", a.tables)
        record("native-load:verified", shape=list(form.m.shape),
               bit_sha256={k: hashlib.sha256(getattr(form, k).bits).hexdigest() for k in "mse"},
               search_solver=search_state(form), solver_factories=solver_count,
               table_fingerprint=table._fp("G"))
        return
    for name in ("enumerate_form", "minimal", "pair_minimal", "generic_filter"):
        original = getattr(E, name)
        def wrapper(*args, _fn=original, _name=name, **kwargs):
            record(_name + ":start")
            result = _fn(*args, **kwargs)
            containers = result if _name == "enumerate_form" else (result,)
            record(_name + ":end", containers=[size(x) for x in containers])
            if _name == "enumerate_form":
                form = args[0]
                record("enumeration:engine", engine=form.enumeration_engine)
                if a.enumeration_only:
                    alive, empty = result
                    before = packed_digest("enumeration", form, alive, empty)
                    entries = len(alive)  # до минимальности: minimal на месте меняет alive
                    if a.with_minimal:
                        record("minimal-only:start")
                        # Как в run(): минимальность на месте, если код её поддерживает
                        # (--copy-minimal — прежняя копия).
                        inplace = hasattr(E, "INPLACE_MINIMAL")
                        mins = E.minimal(alive, inplace=True) if inplace else E.minimal(alive)
                        record("minimal-only:end", entries=len(mins), inplace=inplace and E.INPLACE_MINIMAL)
                        after = packed_digest("minimal", form, mins, empty)
                    else:
                        after = None
                    record("enumeration:verified", entries=entries, empty=len(empty), n_alive=form.n_alive,
                           enumeration_sha256=before, minimal_sha256=after, engine=form.enumeration_engine)
                    raise EnumerationComplete()
            return result
        setattr(E, name, wrapper)
    original = E.cdecide
    calls = 0
    @wraps(original)
    def decide(*args, **kwargs):
        nonlocal calls
        result = original(*args, **kwargs)
        calls += 1
        frame = sys._getframe(1)
        if calls % 5000 == 0 and frame.f_code.co_name == "run":
            loc = frame.f_locals
            memo = loc.get("degen_memo")
            record("verdicts:progress", report_rows=len(loc.get("report", [])),
                   degeneration_targets=len(loc.get("degen", [])),
                   degeneration_cache=size(memo), verdict_cache=size(E.VCACHE_OUT),
                   bank_unsat=sum(len(b.unsat) for b in fast._BANKS.values()),
                   phase_scoped_calls=sum(b.phase_scoped_calls for b in fast._BANKS.values()),
                   phase_max_scope=max((b.phase_max_scope for b in fast._BANKS.values()), default=0))
        return result
    E.cdecide = decide
    original_run = E.run
    @wraps(original_run)
    def run(*args, **kwargs):
        result = original_run(*args, **kwargs)
        form, alive, empty, report = result
        h = hashlib.sha256()
        encoder = json.JSONEncoder(ensure_ascii=False, sort_keys=True, separators=(",", ":"))
        with (gzip.open(out / "report.jsonl.gz", "wb") if a.save_report else nullcontext(None)) as archive:
            for row in report:
                line = encoder.encode(row).encode() + b"\n"
                h.update(line)
                if archive is not None:
                    archive.write(line)
        record("run:end", report_rows=len(report), report_sha256=h.hexdigest(),
               alive=size(alive), empty=size(empty), legacy_stages=form.mem,
               search_solver=search_state(form), solver_factories=solver_count,
               phase_scoped_calls=sum(b.phase_scoped_calls for b in fast._BANKS.values()),
               phase_max_scope=max((b.phase_max_scope for b in fast._BANKS.values()), default=0))
        return result
    E.run = run
    record("start", python=sys.version, table_fingerprint=table._fp("G"),
           bank_models=fast.BANK_MODELS, legacy_empty_cache=a.legacy_empty_cache,
           eager_search=a.eager_search, early_min=E.EARLY_MIN, sparse_leaf=E.SPARSE_LEAF,
           native_enum=E.NATIVE_ENUM, native_minimal=E.NATIVE_MINIMAL,
           scoped_phases=fast.SCOPED_PHASES)
    sys.argv = ["table", "перебор", "G", "--каталог", a.tables, "--выход", str(out / "results"),
                "--схемы", a.scheme, "--нитей", "1", "--посылок", "3", "--предел", str(a.seconds)]
    try:
        table.main()
    except EnumerationComplete:
        pass
    record("end")


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--tables", required=True)
    p.add_argument("--skel", required=True)
    p.add_argument("--library-cache", required=True)
    p.add_argument("--scheme", required=True)
    p.add_argument("--out", required=True)
    p.add_argument("--seconds", type=int, default=180, help="всё время процесса, включая загрузку")
    p.add_argument("--rss-gib", type=float, default=6.4)
    p.add_argument("--legacy-empty-cache", action="store_true")
    p.add_argument("--legacy-table-load", action="store_true")
    p.add_argument("--legacy-phase-scope", action="store_true", help="random phases for the entire theory")
    mode = p.add_mutually_exclusive_group()
    mode.add_argument("--table-only", action="store_true", help="изолировать storage, без теории/SAT/перебора")
    mode.add_argument("--load-only", action="store_true", help="native загрузка с каркасом, без перебора")
    mode.add_argument("--enumeration-only", action="store_true", help="полный числовой перебор, без вердиктов/report")
    p.add_argument("--with-minimal", action="store_true", help="в enumeration-only также проверить повторный minimal")
    p.add_argument("--save-enumeration", action="store_true", help="сохранить все packed keys/support/empty в бинарный файл")
    p.add_argument("--python-enum", action="store_true", help="прежние Python enumerate/minimal")
    p.add_argument("--copy-minimal", action="store_true", help="минимальность с копией (ALGEN_INPLACE_MINIMAL=0)")
    p.add_argument("--eager-search", action="store_true", help="прежнее немедленное создание solver Search")
    p.add_argument("--legacy-leaf-minimal", action="store_true", help="полный обход подусловий без раннего выхода")
    p.add_argument("--legacy-leaf-matrix", action="store_true", help="битовые операции по всем целям листа")
    p.add_argument("--save-report", action="store_true", help="сохранить весь report в gzip по одной строке")
    p.add_argument("--child", action="store_true", help=argparse.SUPPRESS)
    a = p.parse_args()
    if (a.with_minimal or a.save_enumeration) and not a.enumeration_only:
        p.error("with-minimal/save-enumeration требуют enumeration-only")
    if a.enumeration_only and a.save_report:
        p.error("enumeration-only не создаёт полный raw report")
    if a.child:
        child(a)
        return
    for name in ("tables", "skel", "library_cache", "out"):
        setattr(a, name, str(Path(getattr(a, name)).resolve()))
    out = Path(a.out)
    out.mkdir(parents=True, exist_ok=False)
    if a.seconds <= 0 or a.rss_gib <= 0:
        p.error("нужны положительные лимиты времени и RSS")
    env = {k: v for k, v in os.environ.items() if not k.startswith("ALGEN_")}
    env.update(ALGEN_SIZE="2", ALGEN_FAST="1", ALGEN_COMPRESS="1", ALGEN_STATE_SAVE="1",
               ALGEN_SKEL=str(Path(a.skel).resolve()), OPENBLAS_NUM_THREADS="1", OMP_NUM_THREADS="1")
    if a.legacy_empty_cache:
        env["ALGEN_DEGEN_EMPTY_CACHE"] = "1"
    if a.legacy_table_load:
        env["ALGEN_STREAM_TABLE"] = "0"
    if a.legacy_phase_scope:
        env["ALGEN_SCOPED_PHASES"] = "0"
    if a.eager_search:
        env["ALGEN_EAGER_SEARCH"] = "1"
    if a.legacy_leaf_minimal:
        env["ALGEN_EARLY_MIN"] = "0"
    if a.legacy_leaf_matrix:
        env["ALGEN_SPARSE_LEAF"] = "0"
    if a.python_enum:
        env["ALGEN_NATIVE_ENUM"] = env["ALGEN_NATIVE_MINIMAL"] = "0"
    if a.copy_minimal:
        env["ALGEN_INPLACE_MINIMAL"] = "0"
    cmd = [sys.executable, "-B", "-m", "tools.profile_memory", "--child", "--tables", a.tables,
           "--skel", a.skel, "--library-cache", a.library_cache, "--scheme", a.scheme, "--out", a.out,
           "--seconds", str(a.seconds), "--rss-gib", str(a.rss_gib)]
    if a.legacy_empty_cache:
        cmd.append("--legacy-empty-cache")
    if a.legacy_table_load:
        cmd.append("--legacy-table-load")
    if a.legacy_phase_scope:
        cmd.append("--legacy-phase-scope")
    if a.table_only:
        cmd.append("--table-only")
    if a.load_only:
        cmd.append("--load-only")
    if a.eager_search:
        cmd.append("--eager-search")
    if a.legacy_leaf_minimal:
        cmd.append("--legacy-leaf-minimal")
    if a.legacy_leaf_matrix:
        cmd.append("--legacy-leaf-matrix")
    for option in ("enumeration_only", "with_minimal", "save_enumeration", "python_enum", "copy_minimal"):
        if getattr(a, option):
            cmd.append("--" + option.replace("_", "-"))
    if a.save_report:
        cmd.append("--save-report")
    code = {name: hashlib.sha256((Path(__file__).resolve().parents[1] / name).read_bytes()).hexdigest()
            for name in ("algen/enumerate.py", "algen/table.py", "algen/deferred.py", "algen/native_enum.py",
                         "algen/native_enum.cpp", "algen/fast.py", "tools/profile_memory.py")}
    start = time.monotonic()
    reason = "exited"
    sampled = 0
    with (out / "process.log").open("wb") as log, (out / "rss.jsonl").open("w") as trace:
        proc = subprocess.Popen(cmd, cwd=Path(__file__).resolve().parents[1], env=env, stdout=log, stderr=log)
        try:
            while proc.poll() is None:
                memory = rss(proc.pid)
                sampled = max(sampled, memory.get("VmRSS", 0))
                elapsed = time.monotonic() - start
                trace.write(json.dumps(dict(seconds=round(elapsed, 3), **memory)) + "\n")
                trace.flush()
                if sampled > a.rss_gib * 1024**2 or elapsed > a.seconds:
                    reason = "rss_budget" if sampled > a.rss_gib * 1024**2 else "time_budget"
                    proc.terminate()
                    break
                time.sleep(.25)
            try:
                proc.wait(timeout=10)
            except subprocess.TimeoutExpired:
                reason += ":forced_kill"
                proc.kill()
                proc.wait()
        finally:
            if proc.poll() is None:
                proc.kill()
                proc.wait()
    usage = resource.getrusage(resource.RUSAGE_CHILDREN)
    result = dict(scheme=a.scheme, returncode=proc.returncode, stop_reason=reason,
                  wall_seconds=round(time.monotonic()-start, 3), cpu_seconds=usage.ru_utime+usage.ru_stime,
                  peak_rss_kib=usage.ru_maxrss, sampled_rss_kib=sampled,
                  limits=dict(seconds=a.seconds, rss_gib=a.rss_gib), legacy_empty_cache=a.legacy_empty_cache)
    result["legacy_table_load"] = a.legacy_table_load
    result["legacy_phase_scope"] = a.legacy_phase_scope
    report = out / "results" / (a.scheme + ".json")
    result["scheme_status"] = None
    if report.is_file():
        try:
            summary = json.loads(report.read_text())
            if not isinstance(summary, dict):
                raise ValueError("сводка должна быть объектом")
            result["scheme_status"] = summary.get("статус")
        except (OSError, ValueError) as e:
            result["summary_error"] = str(e)
    result["complete"] = reason == "exited" and proc.returncode == 0 and (a.table_only or a.load_only or result["scheme_status"] == "ok")
    if a.enumeration_only:
        receipt = None
        try:
            stages = [json.loads(s) for s in (out / "stages.jsonl").read_text().splitlines()] if (out / "stages.jsonl").exists() else []
            receipt = next((s for s in reversed(stages) if s.get("stage") == "enumeration:verified"), None)
        except (OSError, ValueError, TypeError, AttributeError) as e:
            result["enumeration_receipt_error"] = str(e)
        result["complete"] = reason == "exited" and proc.returncode == 0 and valid_enumeration_receipt(receipt, a.with_minimal)
    result["scope"] = "table storage only" if a.table_only else ("native load only" if a.load_only else ("native enumeration only" if a.enumeration_only else "full native scheme"))
    result["eager_search"] = a.eager_search
    result["early_min"] = not a.legacy_leaf_minimal
    result["sparse_leaf"] = not a.legacy_leaf_matrix
    result["python_enum"] = a.python_enum
    result["with_minimal"] = a.with_minimal
    result["saved_enumeration"] = a.save_enumeration
    result["saved_report"] = a.save_report
    result["code_sha256"] = code
    (out / "measurement.json").write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps(result, ensure_ascii=False))


if __name__ == "__main__":
    main()
