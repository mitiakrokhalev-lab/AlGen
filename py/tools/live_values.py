"""Динамический опыт: значения таблицы → вопросы архива без перепрогона схемы.

    python3 -B -m tools.live_values АРХИВ.db --выгрузка СХЕМА.archive.jsonl.gz [--значения факты.json]

АРХИВ.db — архив live.py (создаётся). Выгрузка — полный отчёт схемы (ALGEN_DYNAMIC_EXPORT=1;
с ALGEN_KNOWLEDGE=1 у вопросов есть вид и корни) — импортируется, если схемы ещё нет. Значения —
список пакетов {"key", "assignment", "facts": {атом: bool|null}, "source": {"kind": "gap"|…,
"reference"}} — конкретные строки (подстановки) с проверенными значениями; каждое применяется
через LiveArchive.apply_example (источник обязателен, «верно» во всех литералах запрета опровергает
вопрос, зависимые свёртки раскрываются, история и отзыв сохраняются). Печатает состояние архива
до и после и опровергнутые вопросы с их видом.
"""
import argparse
import gzip
import json
import sys

from algen.live import LiveArchive


def run(db, export=None, values=None, out=print):
    with LiveArchive(db) as arc:
        ctx = None
        if export:
            with gzip.open(export, "rt", encoding="utf-8") as f:
                header = json.loads(next(f))["header"]
                known = arc.db.execute("SELECT context FROM schemes WHERE name=?", (header.get("scheme"),)).fetchone()
                ctx = known[0] if known else arc.import_report(header, (json.loads(s) for s in f if s.strip()))
        if ctx is None:
            ctx = arc.db.execute("SELECT id FROM contexts ORDER BY rowid LIMIT 1").fetchone()[0]
        before = arc.stats(ctx)
        out(json.dumps({"до": before["states"]}, ensure_ascii=False))
        refuted = []
        for packet in values or []:
            arc.apply_example(ctx, packet)
            for qid, payload in arc.db.execute(
                    "SELECT q.id, q.payload FROM refutations r JOIN examples e ON e.id = r.example "
                    "JOIN questions q ON q.id = r.question WHERE e.active = 1 AND e.name = ? AND q.context = ?",
                    (packet["key"], ctx)):
                p = json.loads(payload)
                refuted.append({"вопрос": " & ".join(p.get("запрет", [])), "вид": p.get("вид"), "строка": packet["key"]})
        after = arc.stats(ctx)
        out(json.dumps({"после": after["states"], "задания": after["pending"]}, ensure_ascii=False))
        for r in refuted:
            out(json.dumps(r, ensure_ascii=False))
        return before, after, refuted


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("архив")
    ap.add_argument("--выгрузка")
    ap.add_argument("--значения")
    a = ap.parse_args(argv)
    values = json.load(open(a.значения, encoding="utf-8")) if a.значения else []
    run(a.архив, a.выгрузка, values)
    return 0


if __name__ == "__main__":
    sys.exit(main())
