"""Возобновляемый исполнитель enumerate/compress с проверяемым завершением.

План фиксирует только уже импортированные полные схемы. Старые архивы без
параметров генерации требуют повторного экспорта. Незавершённый/устаревший
прогон сохраняется для диагностики и никогда не снимает долг очереди.
"""

import argparse
from contextlib import contextmanager
import fcntl
import gzip
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sqlite3
import sys
import time
import uuid

from .live import LiveArchive, digest, dumps


def file_hash(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for block in iter(lambda: f.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def implementation_hash():
    root = Path(__file__).resolve().parent
    sources = (p for p in root.iterdir() if p.is_file() and p.suffix in {".py", ".cpp", ".h", ".hpp"})
    return digest([(p.name, file_hash(p)) for p in sorted(sources)])


def data_hash():
    root = Path(__file__).resolve().parents[2] / "data"
    return digest([(str(p.relative_to(root)), file_hash(p)) for p in sorted(root.rglob("*")) if p.is_file()])


def table_hashes(directory, base):
    paths = sorted({p for b in {base, "G"} for p in Path(directory).glob(b + ".*-*.pickle")})
    if not paths:
        raise ValueError("нет частей таблицы базы")
    paths = sorted(set(paths) | {p for b in {base, "G"} for p in [Path(directory) / (b + ".rep.pickle")] if p.is_file()})
    return {p.name: file_hash(p) for p in paths}


def scope(archive, ctx):
    rows = list(archive.db.execute("SELECT s.name,s.complete,h.header FROM schemes s LEFT JOIN scheme_headers h "
                                   "ON h.context=s.context AND h.name=s.name WHERE s.context=? ORDER BY s.name", (ctx,)))
    if not rows or any(not r["complete"] or not r["header"] for r in rows):
        raise ValueError("нужны полные экспорты всех импортированных схем")
    headers = [json.loads(r["header"]) for r in rows]
    if any(not isinstance(h.get("generation"), dict) for h in headers):
        raise ValueError("старый экспорт без generation: повторите полный экспорт, параметры не угадываются")
    common = {k: v for k, v in headers[0]["generation"].items() if k not in ("k", "terms")}
    required = {"size", "fast", "k_spec", "term_limit", "skip", "defer", "close_marked", "compress"}
    if (set(common) != required or common["skip"] or common["defer"] or not common["close_marked"]
            or type(common["size"]) is not int or common["size"] <= 0):
        raise ValueError("неподдерживаемая или ограниченная область generation")
    for h in headers:
        g = h["generation"]
        if ({k: v for k, v in g.items() if k not in ("k", "terms")} != common
                or type(g.get("k")) is not int or not isinstance(g.get("terms"), list)):
            raise ValueError("разные/неполные параметры генерации в одном контексте")
    return headers, common


def snapshot_token(archive, ctx):
    headers, _ = scope(archive, ctx)
    row = archive.db.execute("SELECT revision FROM contexts WHERE id=?", (ctx,)).fetchone()
    return {"revision": row[0], "content": archive.fingerprint(ctx), "scope": digest(headers)}


@contextmanager
def worker_lock(db_path):
    # flock освобождается ОС и после аварии. Другие обновления БД не блокируются.
    with open(str(db_path) + ".worker.lock", "a") as f:
        try:
            fcntl.flock(f, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as e:
            raise ValueError("этот архив уже обслуживает другой worker") from e
        try:
            yield
        finally:
            fcntl.flock(f, fcntl.LOCK_UN)


def freeze(source, ctx, path):
    """Малый снимок только контекста и активных строк; большие records не копируются."""
    with LiveArchive(path) as target:
        target.db.execute("INSERT INTO contexts SELECT ?,?,?", tuple(source.db.execute(
            "SELECT id,header,revision FROM contexts WHERE id=?", (ctx,)).fetchone()))
        with target.transaction():
            for r in source.db.execute("SELECT * FROM examples WHERE context=? AND active=1", (ctx,)):
                target.db.execute("INSERT INTO examples VALUES(?,?,?,?,?,?,?)", tuple(r))
                target.db.execute("INSERT INTO example_hashes VALUES(?,?)", (r["id"], source.db.execute(
                    "SELECT content FROM example_hashes WHERE example=?", (r["id"],)).fetchone()[0]))
                target.db.executemany("INSERT INTO facts VALUES(?,?,?)", ((r["id"], a, v) for a, v in source.db.execute(
                    "SELECT atom,value FROM facts WHERE example=?", (r["id"],))))


def create_plan(db_path, ctx, tables, directory):
    directory = Path(directory).resolve()
    directory.mkdir(parents=True, exist_ok=False)
    tables = str(Path(tables).resolve())
    with LiveArchive(db_path) as a, a.transaction():
        a._writable(ctx)
        headers, generation = scope(a, ctx)
        h = json.loads(a.db.execute("SELECT header FROM contexts WHERE id=?", (ctx,)).fetchone()[0])
        token = snapshot_token(a, ctx)
        jobs = [dict(r) for r in a.db.execute("SELECT kind,revision FROM jobs WHERE context=? ORDER BY kind", (ctx,))]
        if not jobs:
            raise ValueError("в этом контексте нет долга очереди")
        freeze(a, ctx, directory / "input.sqlite")
        manifest = {"version": 1, "id": uuid.uuid4().hex, "context": ctx, "header": h,
                    "token": token, "jobs": jobs, "generation": generation,
                    "schemes": {x["scheme"]: x["generation"] for x in headers},
                    "tables": tables, "table_hashes": table_hashes(tables, h["base"]),
                    "implementation": implementation_hash(), "directory": str(directory)}
        manifest["data"] = data_hash()
        manifest["input_file"] = file_hash(directory / "input.sqlite")
        a.db.execute("INSERT INTO worker_runs(id,context,manifest,status) VALUES(?,?,?,'planned')",
                     (manifest["id"], ctx, dumps(manifest)))
        (directory / "plan.json").write_text(dumps(manifest), encoding="utf-8")
        return manifest


def check_inputs(a, m):
    a._writable(m["context"])
    if snapshot_token(a, m["context"]) != m["token"]:
        raise ValueError("исходная библиотека или область изменилась; нужен новый план")
    if implementation_hash() != m["implementation"]:
        raise ValueError("изменился код; нужен новый план")
    if data_hash() != m["data"]:
        raise ValueError("изменились данные; нужен новый план")
    if table_hashes(m["tables"], m["header"]["base"]) != m["table_hashes"]:
        raise ValueError("изменились таблицы; нужен новый план")
    if file_hash(Path(m["directory"]) / "input.sqlite") != m["input_file"]:
        raise ValueError("повреждён снимок входных строк")


def commands(m, results, staged, state, limit, memory):
    """Аргументы формируются здесь, команда из внешнего JSON не исполняется."""
    g, h = m["generation"], m["header"]
    cmd = [sys.executable, "-B", "-m", "algen.live_exec", "algen.table", "перебор", h["base"],
           "--каталог", m["tables"], "--выход", str(results), "--нитей", "1",
           "--посылок", g["k_spec"], "--схемы", ",".join(sorted(m["schemes"])),
           "--предел", str(limit), "--память", str(memory)]
    if g["term_limit"] is not None:
        cmd += ["--термов", str(g["term_limit"])]
    env = {k: v for k, v in os.environ.items() if not k.startswith("ALGEN_")}
    env.update(ALGEN_SIZE=str(g["size"]), ALGEN_CLASS=h["class"], ALGEN_DYNAMIC_EXPORT="1",
               ALGEN_STATE_SAVE="1", ALGEN_DYNAMIC_DB=str(Path(m["directory"]) / "input.sqlite"),
               ALGEN_DYNAMIC_CONTEXT=m["context"], ALGEN_WORKER_RUN=m["id"],
               ALGEN_WORKER_CACHE=str(Path(m["directory"]) / "library-cache"))
    if g["fast"]:
        env["ALGEN_FAST"] = "1"
    if g["compress"]:
        env["ALGEN_COMPRESS"] = "1"
    if state:
        env["ALGEN_STATE"] = str(Path(state).resolve())
    basis = [sys.executable, "-B", "-m", "algen.live_exec", "algen.compress_base", h["base"], str(results),
             "--класс", h["class"], "--live-db", str(staged), "--live-context", "TARGET",
             "--полная-проверка", "--выход", str(results.parent / "basis.json")]
    return cmd, basis, env


def run_command(argv, env, log):
    with open(log, "ab") as f:
        subprocess.run(argv, cwd=Path(__file__).resolve().parents[1], env=env,
                       stdout=f, stderr=subprocess.STDOUT, check=True)


def save_receipt(root, receipt):
    # Источник истины — committed worker_runs.detail. Нехватка диска для
    # дополнительной копии не отменяет уже опубликованное поколение.
    try:
        (root / "receipt.json").write_text(dumps(receipt), encoding="utf-8")
    except OSError:
        pass


def validate_exports(m, results, only=None):
    expected = set(m["schemes"]) if only is None else set(only)
    actual = {p.name.removesuffix(".archive.jsonl.gz") for p in results.glob("*.archive.jsonl.gz")}
    if only is None and actual != expected:
        raise ValueError("набор полных экспортов не совпал с планом")
    fingerprint = None
    files = {}
    for sid in sorted(expected):
        p = results / (sid + ".archive.jsonl.gz")
        summary = json.loads((results / (sid + ".json")).read_text(encoding="utf-8"))
        if summary.get("статус") != "ok" or summary.get("строк противоречат базе") != 0:
            raise ValueError("неуспешная схема/противоречащие строки: " + sid)
        with sqlite3.connect(results.parent / ("validation-" + uuid.uuid4().hex + ".sqlite")) as classes, gzip.open(p, "rt", encoding="utf-8") as f:
            classes.execute("CREATE TABLE classes(signature TEXT PRIMARY KEY,verdict TEXT)")
            h = json.loads(next(f))["header"]
            if (h.get("format") != "algen.full-report" or h.get("version") != 1 or h.get("complete") is not True
                    or h.get("worker_run") != m["id"] or h.get("scheme") != sid
                    or h.get("generation") != m["schemes"][sid]
                    or any(h.get(k) != v for k, v in m["header"].items() if k != "library")
                    or h.get("dynamic") != {"context": m["context"], "revision": m["token"]["revision"],
                                             "rows": m["example_count"]}):
                raise ValueError("экспорт не соответствует замороженному плану: " + sid)
            if not h.get("library") or h["library"] != summary.get("отпечаток"):
                raise ValueError("отпечатки сводки и экспорта расходятся")
            fingerprint = fingerprint or h["library"]
            if fingerprint != h["library"]:
                raise ValueError("схемы относятся к разным снимкам библиотеки")
            counts, uncond = {}, 0
            for line in f:  # прочитать до конца: gzip CRC, обрыв и число записей
                row = json.loads(line)
                verdict = row.get("вердикт", "")
                if verdict.startswith("ОШИБКА") or row.get("ОШИБКА сжатия"):
                    raise ValueError("ошибка вердикта: " + sid)
                if row.get("type") == "unconditional":
                    uncond += 1
                else:
                    counts[verdict] = counts.get(verdict, 0) + 1
                    classes.execute("INSERT OR IGNORE INTO classes VALUES(?,?)",
                                    (dumps(row["класс"]), verdict))
            tally = dict(classes.execute("SELECT verdict,count(*) FROM classes GROUP BY verdict"))
            if (sum(counts.values()) != h.get("report_count") or uncond != h.get("unconditional_count")
                    or tally != summary.get("вердикты") or uncond != len(summary.get("факты без посылок", []))):
                raise ValueError("число/вердикты записей расходятся со сводкой: " + sid)
        files[sid] = file_hash(p)
    return files


def prepare_resume(m, results):
    """Нельзя пропустить файл только по заголовку. Повреждённые сохраняются."""
    for sid in m["schemes"]:
        files = [results / (sid + suffix) for suffix in (".json", ".archive.jsonl.gz")]
        if not any(p.exists() for p in files):
            continue
        try:
            validate_exports(m, results, only=[sid])
        except (ValueError, OSError, EOFError, KeyError, StopIteration):
            backup = results.parent / "rejected" / uuid.uuid4().hex
            backup.mkdir(parents=True)
            for p in files:
                if p.exists():
                    p.rename(backup / p.name)


def install_basis(a, ctx, basis):
    """Установка проверенного графа. Вызывается только внутри publish transaction."""
    from .compress_base import archive_questions, questions_hash
    qs = archive_questions(a, ctx)
    ids = {q["id"] for q in qs}
    kept, folded = basis["оставлено"], basis["свёрнуто"]
    ks = set(kept)
    v = basis.get("verify", {})
    theory = json.loads(a.db.execute("SELECT header FROM contexts WHERE id=?", (ctx,)).fetchone()[0])["theory"]
    if (basis.get("context") != ctx or basis.get("theory") != theory
            or basis.get("input_hash") != questions_hash(qs) or basis.get("input_count") != len(qs)
            or v.get("full") is not True or v.get("нарушений") != 0 or v.get("checked") != len(folded)
            or len(kept) != len(ks) or ks & set(folded) or ks | set(folded) != ids
            or any(not deps or any(d not in ks for d in deps) for deps in folded.values())
            or any(str(reason).startswith("ОШИБКА") for reason in basis.get("особые", {}).values())):
        raise ValueError("базис не имеет полной проверки/покрытия текущих открытых вопросов")
    for qid in ids:
        a.db.execute("DELETE FROM dependencies WHERE child=?", (qid,))
        a.db.execute("DELETE FROM unresolved WHERE child=?", (qid,))
        is_folded = qid in folded
        a.db.execute("UPDATE questions SET folded=?,invalidated=0,state=? WHERE id=?",
                     (int(is_folded), "folded" if is_folded else "open", qid))
        a.db.executemany("INSERT INTO dependencies VALUES(?,?)", ((qid, d) for d in folded.get(qid, [])))
    a._check_cycles(ctx)


def execute(db_path, run_id, *, state=None, limit=3600, memory=2, runner=run_command):
    with worker_lock(db_path), LiveArchive(db_path) as a:
        row = a.db.execute("SELECT * FROM worker_runs WHERE id=?", (run_id,)).fetchone()
        if row is None:
            raise ValueError("нет плана")
        if row["status"] == "completed":
            receipt = json.loads(row["detail"])
            save_receipt(Path(json.loads(row["manifest"])["directory"]), receipt)
            return receipt
        m = json.loads(row["manifest"])
        root = Path(m["directory"])
        start = time.monotonic()
        try:
            check_inputs(a, m)
            with LiveArchive(root / "input.sqlite") as inp:
                m["example_count"] = inp.stats(m["context"])["examples"]
            a.db.execute("UPDATE worker_runs SET status='running' WHERE id=?", (run_id,))
            results = root / "results"
            results.mkdir(exist_ok=True)
            # Каждый повтор строит новый staging, прежние артефакты не удаляются.
            staged = root / ("staging-" + uuid.uuid4().hex + ".sqlite")
            enum_cmd, basis_cmd, env = commands(m, results, staged, state, limit, memory)
            prepare_resume(m, results)
            runner(enum_cmd, env, root / "enumerate.log")
            files = validate_exports(m, results)
            with LiveArchive(staged) as stage:
                # Сохраняем исходные ID примеров для совпадения provenance при publish.
                with LiveArchive(root / "input.sqlite") as inp:
                    stage.db.execute("INSERT INTO contexts VALUES(?,?,?)", tuple(inp.db.execute(
                        "SELECT * FROM contexts WHERE id=?", (m["context"],)).fetchone()))
                    for table in ("examples", "example_hashes", "facts"):
                        for r in inp.db.execute("SELECT * FROM " + table):
                            stage.db.execute("INSERT INTO " + table + " VALUES(" + ",".join("?" for _ in r) + ")", tuple(r))
                target = None
                for sid in sorted(m["schemes"]):
                    ctx = stage.import_file(results / (sid + ".archive.jsonl.gz"))
                    if ctx == m["context"] or (target and target != ctx):
                        raise ValueError("нет единственного нового поколения")
                    target = ctx
                stage.carry_examples(m["context"], target)
            basis_cmd[basis_cmd.index("TARGET")] = target
            # Возобновление сжатия не доверяет прежнему JSON: снова SAT-проверка всех связей.
            runner(basis_cmd, env, root / "compress.log")
            basis = json.loads((root / "basis.json").read_text(encoding="utf-8"))
            with LiveArchive(staged) as stage, stage.transaction():
                install_basis(stage, target, basis)
            # Код/таблицы, библиотека и область должны оставаться прежними до публикации.
            check_inputs(a, m)
            if files != validate_exports(m, results):
                raise ValueError("экспорты изменились во время сжатия")
            receipt = {"target": target, "source": m["context"], "run": run_id,
                       "schemes": len(files), "exports": files, "basis_sha256": file_hash(root / "basis.json"),
                       "basis_kept": len(basis["оставлено"]), "basis_folded": len(basis["свёрнуто"]),
                       "seconds": round(time.monotonic() - start, 3), "scope": "imported complete schemes"}
            with a.transaction():
                check_inputs(a, m)
                if a.db.execute("SELECT 1 FROM contexts WHERE id=?", (target,)).fetchone():
                    raise ValueError("целевой снимок уже существует; его изменения нельзя закрыть этим планом")
                for sid in sorted(m["schemes"]):
                    if a.import_file(results / (sid + ".archive.jsonl.gz")) != target:
                        raise ValueError("публикуется другой контекст")
                a.carry_examples(m["context"], target)
                install_basis(a, target, basis)
                for job in m["jobs"]:
                    a.db.execute("DELETE FROM jobs WHERE context=? AND kind=? AND revision=?",
                                 (m["context"], job["kind"], job["revision"]))
                a.db.execute("DELETE FROM jobs WHERE context=?", (target,))
                a.db.execute("INSERT INTO successors VALUES(?,?,?)", (m["context"], target, run_id))
                a.db.execute("UPDATE worker_runs SET status='completed',detail=? WHERE id=?", (dumps(receipt), run_id))
            save_receipt(root, receipt)
            return receipt
        except BaseException as e:
            a.db.execute("UPDATE worker_runs SET status='failed',detail=? WHERE id=? AND status!='completed'",
                         (dumps({"error": str(e), "seconds": round(time.monotonic() - start, 3)}), run_id))
            raise


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("db")
    sub = p.add_subparsers(dest="command", required=True)
    c = sub.add_parser("plan")
    c.add_argument("context")
    c.add_argument("--tables", required=True)
    c.add_argument("--out", required=True)
    c = sub.add_parser("run")
    c.add_argument("id")
    c.add_argument("--state")
    c.add_argument("--limit", type=float, default=3600)
    c.add_argument("--memory", type=float, default=2, help="дополнительный лимит RLIMIT_AS дочерней схемы, GB")
    a = p.parse_args()
    result = (create_plan(a.db, a.context, a.tables, a.out) if a.command == "plan"
              else execute(a.db, a.id, state=a.state, limit=a.limit, memory=a.memory))
    print(dumps(result))


if __name__ == "__main__":
    main()
