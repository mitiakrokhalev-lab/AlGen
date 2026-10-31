"""Пакетный перебор: много схем в одном процессе (библиотека грузится один раз),
параллельно по ядрам, с продолжением после остановки и общей сводкой.

Файл схем — по строке на схему: «id | условие | термы через ;». Пустое условие —
основная форма G, N, G/N. Строки с «#» — комментарии.

    cd py
    python3 -m algen.batch прогон ../data/schemes/grp.txt --каталог ../кэш/прогон --нитей 2
    python3 -m algen.batch прогон … --часть 3/20        # только каждая 20-я схема, начиная с 3-й
    python3 -m algen.batch сводка ../кэш/прогон          # общий отчёт по всем схемам

Для каждой схемы пишутся <id>.txt (выдача, как у algen.enumerate) и <id>.json
(сводка). Схема пропускается, если её JSON уже посчитан при тех же данных и коде.
"""

import argparse
import io
import json
import multiprocessing as mp
import os
import sys
import time
import traceback
from collections import defaultdict
from pathlib import Path

from . import enumerate as E
from .library import _fingerprint, built_library
from .logic import Vocab

_STATE = {}


def read_schemes(path):
    out = []
    for line in Path(path).read_text(encoding="utf-8").splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        parts = [x.strip() for x in line.split("|")]
        sid, decl, terms = (parts + ["", ""])[:3]
        out.append({"id": sid, "условие": decl, "термы": [t.strip() for t in terms.split(";") if t.strip()]})
    return out


def _one(job):
    sch, k, outdir, fp = job
    lib, vocab = _STATE["lib"], _STATE["vocab"]
    out, err = io.StringIO(), io.StringIO()
    t0 = time.time()
    try:
        if sch["условие"]:
            form = E.SchemeForm(lib, vocab, sch["условие"], sch["термы"])
            form, alive, empty, report = E.run(k, lib, vocab, form)
        else:
            form, alive, empty, report = E.run(k, lib, vocab)
        summary = E.render(form, alive, empty, report, out=out, err=err, registry=_STATE["registry"])
        status = "ok"
    except Exception:
        summary, status = {}, "ошибка"
        err.write(traceback.format_exc())
    rec = {"id": sch["id"], "условие": sch["условие"], "термы": sch["термы"], "посылок": k,
           "без": sorted(E.SKIP), "отпечаток": fp, "секунд": round(time.time() - t0, 1),
           "статус": status, **summary}
    base = Path(outdir) / sch["id"]
    base.with_suffix(".txt").write_text(err.getvalue() + "\n" + out.getvalue(), encoding="utf-8")
    base.with_suffix(".json").write_text(json.dumps(rec, ensure_ascii=False, indent=1), encoding="utf-8")
    return sch["id"], status, rec["секунд"], summary.get("остаток")


def run_batch(a):
    E.SKIP.update(x.strip() for x in a.skip.split(",") if x.strip())
    schemes = read_schemes(a.file)
    if a.part:
        i, n = map(int, a.part.split("/"))
        schemes = schemes[i - 1::n]
    outdir = Path(a.dir)
    outdir.mkdir(parents=True, exist_ok=True)
    vocab = Vocab.section("grp")
    _STATE.update(lib=built_library(vocab), vocab=vocab, registry=E.load_registry())
    fp = _fingerprint() + ":" + ",".join(sorted(E.SKIP)) + f":{a.k}"
    todo = []
    for s in schemes:
        j = outdir / f"{s['id']}.json"
        if j.exists() and not a.force:
            try:
                old = json.loads(j.read_text(encoding="utf-8"))
                if old.get("отпечаток") == fp and old.get("статус") == "ok":
                    continue
            except Exception:
                pass
        todo.append((s, a.k, str(outdir), fp))
    print(f"схем {len(schemes)}, считать {len(todo)}, нитей {a.jobs}", file=sys.stderr)
    t0 = time.time()
    ctx = mp.get_context("fork")  # библиотека наследуется без копирования
    running, queue, done = {}, list(todo), 0

    def child(job, limit):
        if limit:
            import resource
            resource.setrlimit(resource.RLIMIT_AS, (limit, limit))
        try:
            _one(job)
        except MemoryError:
            os._exit(3)
        os._exit(0)

    while queue or running:
        while queue and len(running) < a.jobs:
            job = queue.pop(0)
            p = ctx.Process(target=child, args=(job, int(a.mem * 2**30) if a.mem else 0))
            p.start()
            running[p] = (job, time.time())
        for p in list(running):
            if p.exitcode is None:
                continue
            job, st = running.pop(p)
            done += 1
            sid = job[0]["id"]
            if p.exitcode != 0:  # убит (память) или упал: отметить, чтобы видеть в сводке
                why = "память" if p.exitcode in (3, -9) else f"код {p.exitcode}"
                base = Path(job[2]) / sid
                base.with_suffix(".json").write_text(json.dumps(
                    {"id": sid, "условие": job[0]["условие"], "термы": job[0]["термы"], "отпечаток": job[3],
                     "статус": f"ошибка: {why}", "секунд": round(time.time() - st, 1)}, ensure_ascii=False, indent=1),
                    encoding="utf-8")
                print(f"[{done}/{len(todo)}] {sid}: ошибка ({why})", file=sys.stderr, flush=True)
            else:
                rec = json.loads((Path(job[2]) / f"{sid}.json").read_text(encoding="utf-8"))
                print(f"[{done}/{len(todo)}] {sid}: {rec['статус']}, {rec['секунд']} с, остаток {rec.get('остаток')}",
                      file=sys.stderr, flush=True)
        time.sleep(0.2)
    print(f"готово за {round(time.time() - t0)} с", file=sys.stderr)


def aggregate(a):
    """Общая сводка: решающие значения по всем схемам (повторы складываются),
    вопросы реестра, кластеры без кандидата, таблица схем."""
    recs = []
    for p in sorted(Path(a.dir).glob("*.json")):
        try:
            r = json.loads(p.read_text(encoding="utf-8"))
        except Exception as e:
            print(f"{p.name}: не читается ({e})", file=sys.stderr)
            continue
        if isinstance(r, dict) and "id" in r:
            recs.append(r)
    vals = defaultdict(lambda: {"схем": 0, "запретов": 0, "пример": None})
    reg = defaultdict(lambda: {"схем": 0, "запретов": 0})
    hidden = defaultdict(lambda: {"схем": 0, "запретов": 0})
    lines = []
    for r in recs:
        if r.get("статус") != "ok":
            lines.append(f"| {r['id']} | {r.get('статус')} | | | | {r.get('секунд')} |")
            continue
        for v in r.get("значения", []):
            x = vals[v["имя"]]
            x["схем"] += 1
            x["запретов"] += v["запретов"]
            x["пример"] = x["пример"] or f"{r['id']}: {v['пример']}"
        for k, n in r.get("реестр", {}).items():
            reg[k]["схем"] += 1
            reg[k]["запретов"] += n
        for kind in ("трудный контрпример", "короткий довод"):
            for f, n in r.get(kind, {}).items():
                hidden[(kind, f)]["схем"] += 1
                hidden[(kind, f)]["запретов"] += n
        v = r.get("вердикты", {})
        lines.append(f"| {r['id']} | {r.get('запретов')} | {v.get('выводится', 0)} | {r.get('остаток')} | "
                     f"{len(r.get('значения', []))} / {sum(len(c['третьи']) for c in r.get('без кандидата', []))} | {r.get('секунд')} |")
    from collections import Counter
    st = Counter(r.get("статус") for r in recs)
    ok = [r for r in recs if r.get("статус") == "ok"]
    head = (f"Схем: {len(recs)}; " + ", ".join(f"{k}: {n}" for k, n in st.most_common()) +
            f". Выводится: {sum(r.get('вердикты', {}).get('выводится', 0) for r in ok)}, "
            f"остаток: {sum(r.get('остаток') or 0 for r in ok)}, "
            f"секунд на схему: среднее {round(sum(float(r.get('секунд') or 0) for r in recs) / max(1, len(recs)))}, "
            f"наибольшее {max((float(r.get('секунд') or 0) for r in recs), default=0)}.\n")
    md = [f"# Сводка пакетного прогона\n\n{head}",
          "## Решающие значения (по всем схемам)\n", "| значение | схем | запретов | пример |", "|---|---|---|---|"]
    for name, x in sorted(vals.items(), key=lambda kv: (-kv[1]["запретов"], kv[0])):
        md.append(f"| {name} | {x['схем']} | {x['запретов']} | {x['пример']} |")
    md += ["\n## Вопросы из реестра\n", "| № | схем | запретов |", "|---|---|---|"]
    md += [f"| {k} | {x['схем']} | {x['запретов']} |" for k, x in sorted(reg.items(), key=lambda kv: -kv[1]["запретов"])]
    md += ["\n## Решающие факты с пометками (трудный контрпример, короткий довод)\n", "| вид | факт | схем | запретов |", "|---|---|---|---|"]
    md += [f"| {k[0]} | {k[1]} | {x['схем']} | {x['запретов']} |" for k, x in sorted(hidden.items(), key=lambda kv: -kv[1]["запретов"])]
    md += ["\n## Схемы\n", "| id | запретов | выводится | остаток | значений / без кандидата | секунд |", "|---|---|---|---|---|---|"] + lines
    out = Path(a.dir) / "сводка.md"
    out.write_text("\n".join(md) + "\n", encoding="utf-8")
    print(out)


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    sub = ap.add_subparsers(dest="cmd", required=True)
    r = sub.add_parser("прогон")
    r.add_argument("file")
    r.add_argument("--каталог", dest="dir", required=True)
    r.add_argument("--нитей", dest="jobs", type=int, default=mp.cpu_count())
    r.add_argument("--посылок", dest="k", type=int, default=2)
    r.add_argument("--часть", dest="part", help="i/n — только схемы с номерами i, i + n, …")
    r.add_argument("--без", dest="skip", default="")
    r.add_argument("--заново", dest="force", action="store_true")
    r.add_argument("--память", dest="mem", type=float, default=3.0, help="ГБ на одну схему (0 — без предела)")
    s = sub.add_parser("сводка")
    s.add_argument("dir")
    a = ap.parse_args()
    run_batch(a) if a.cmd == "прогон" else aggregate(a)


if __name__ == "__main__":
    main()
