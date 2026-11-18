"""Динамический опыт: значения таблицы → вопросы архива без перепрогона схемы.

    python3 -B -m tools.live_values АРХИВ.db --выгрузка СХЕМА.archive.jsonl.gz [--значения факты.json]
        [--строки-было старые.rows.jsonl.gz --строки-стало новые.rows.jsonl.gz]

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
import zlib
from itertools import zip_longest

from algen.live import LiveArchive, VERSION, context_identity, digest, dumps


def _export_header(stream):
    """Accept a complete v1 export, including the promised record count."""
    try:
        header = json.loads(next(stream))["header"]
    except (StopIteration, KeyError, TypeError) as error:
        raise ValueError("нет полного заголовка выгрузки") from error
    if (not isinstance(header, dict) or header.get("format") != "algen.full-report"
            or type(header.get("version")) is not int or header["version"] != VERSION
            or header.get("complete") is not True
            or not isinstance(header.get("scheme"), str) or not header["scheme"]):
        raise ValueError("нужна полная выгрузка algen.full-report текущей версии")
    for name in ("report_count", "unconditional_count"):
        if type(header.get(name)) is not int or header[name] < 0:
            raise ValueError("нет точного счётчика записей выгрузки")
    context_identity(header)
    return header


def _report_rows(stream, header):
    expected = header["report_count"] + header["unconditional_count"]
    seen = 0
    for line in stream:
        if not line.strip():
            continue
        row = json.loads(line)
        seen += 1
        if not isinstance(row, dict) or seen > expected:
            raise ValueError("записи выгрузки не соответствуют заголовку")
        yield row
    if seen != expected:
        raise ValueError("выгрузка обрезана: не все обещанные записи сохранены")


def _existing_context(arc, requested=None):
    if requested is None:
        contexts = arc.db.execute("SELECT id FROM contexts LIMIT 2").fetchall()
        if len(contexts) != 1:
            raise ValueError("нужен --контекст: в архиве нет единственного контекста")
        requested = contexts[0][0]
    if not arc.db.execute("SELECT 1 FROM contexts WHERE id=?", (requested,)).fetchone():
        raise ValueError("неизвестный контекст архива")
    arc._writable(requested)
    return requested


def _reuse_report(arc, ctx, header, stream, known_header):
    """Reuse only the identical full export; never replace saved history."""
    if dumps(header) != known_header:
        raise ValueError("выгрузка изменилась в уже импортированной схеме")
    stored = arc.db.execute("SELECT payload FROM records WHERE context=? AND scheme=? ORDER BY position",
                            (ctx, header["scheme"]))
    missing = object()
    for old, new in zip_longest(stored, _report_rows(stream, header), fillvalue=missing):
        if (old is missing or new is missing
                or zlib.decompress(old[0]).decode() != dumps(new)):
            raise ValueError("выгрузка изменилась в уже импортированной схеме")
    arc._writable(ctx)


def read_rows(path):
    """Строки схемы из <схема>.rows.jsonl.gz (ALGEN_ROW_FACTS=1): ключ → (подстановка, где, {атом: bool})."""
    with gzip.open(path, "rt", encoding="utf-8") as f:
        names = json.loads(next(f))["атомы"]
        out = {}
        for line in f:
            r = json.loads(line)
            facts = {names[j]: True for j in r["t"]}
            facts.update({names[j]: False for j in r["f"]})
            out[r["key"]] = (r["assignment"], r["where"], facts)
    return out


def packets_from_rows(old, new, reference, kind="library"):
    """Пакеты для строк, у которых в новых таблицах прибавились значения: все известные значения
    новой строки (прежние + новые). Расхождение значения — ошибка (новое знание не отменяет старое)."""
    a, b = read_rows(old), read_rows(new)
    packets, added, conflicts, lost = [], 0, [], []
    for key, (assignment, where, facts) in b.items():
        prev = a.get(key, (None, None, {}))[2]
        flips = [x for x, v in prev.items() if x in facts and facts[x] != v]
        if flips:
            conflicts.append((where, flips[:5]))
            continue
        gone = [x for x in prev if x not in facts and x in b_names(b)]
        if gone:  # значение было и пропало — не новое знание; в архив не подаётся
            lost.append((where, gone[:5]))
        gain = [x for x in facts if x not in prev]
        if gain:
            added += len(gain)
            packets.append({"key": key, "assignment": assignment, "facts": facts,
                            "source": {"kind": kind, "reference": reference, "where": where}})
    packets_from_rows.lost = lost
    return packets, added, conflicts


def b_names(rows, _cache={}):
    """Имена атомов снимка (по фактам строк) — чтобы «пропавшим» не считать атом, которого нет в схеме."""
    k = id(rows)
    if k not in _cache:
        _cache.clear()
        _cache[k] = {x for _a, _w, facts in rows.values() for x in facts}
    return _cache[k]


def reclassify(arc, ctx, rows_path):
    """Переразметка A/B/C открытых и свёрнутых вопросов архива по снимку строк (без перепрогона):
    формула варианта (запрет + закреплённые) против известных значений строк — как в
    algen/knowledge.py. Возвращает {вопрос: (прежний вид, новый вид, строк с одним неизвестным)}."""
    import numpy as np
    with gzip.open(rows_path, "rt", encoding="utf-8") as f:
        names = json.loads(next(f))["атомы"]
        rows = [json.loads(line) for line in f]
    col = {n: i for i, n in enumerate(names)}
    T = np.zeros((len(rows), len(names)), dtype=bool)
    F = np.zeros_like(T)
    for r, x in enumerate(rows):
        T[r, x["t"]] = True
        F[r, x["f"]] = True
    out = {}
    for qid, payload in arc.db.execute(
            "SELECT id, payload FROM questions WHERE context=? AND verdict='неизвестно' AND state IN ('open','folded')",
            (ctx,)).fetchall():
        p = json.loads(payload)
        formula = [v[0] for v in arc.db.execute("SELECT formula FROM variants WHERE question=?", (qid,)).fetchall()]
        lits = json.loads(formula[0]) if formula else p.get("запрет", [])
        ok = np.ones(len(rows), dtype=bool)
        unknown = np.zeros(len(rows), dtype=np.int64)
        for lit in lits:
            neg = lit.startswith("¬")
            name = lit[1:] if neg else lit
            j = col.get(name)
            if j is None:  # атома нет в снимке — значение неизвестно во всех строках
                unknown += 1
                continue
            true, false = (F[:, j], T[:, j]) if neg else (T[:, j], F[:, j])
            ok &= ~false
            unknown += ~true & ~false
        alltrue, single, multi = ok & (unknown == 0), ok & (unknown == 1), ok & (unknown >= 2)
        kind = "R" if alltrue.any() else "A" if single.any() else "B" if multi.any() else "C"
        out[qid] = (p.get("вид"), kind, int(single.sum()))
    return out


def run(db, export=None, values=None, out=print, *, context=None):
    with LiveArchive(db) as arc:
        ctx = None
        if export:
            with gzip.open(export, "rt", encoding="utf-8") as f:
                header = _export_header(f)
                ctx = digest(context_identity(header))
                if context is not None and context != ctx:
                    raise ValueError("--контекст не совпадает с контекстом выгрузки")
                known = arc.db.execute("SELECT header FROM scheme_headers WHERE context=? AND name=?",
                                       (ctx, header["scheme"])).fetchone()
                if known:
                    _reuse_report(arc, ctx, header, f, known[0])
                else:
                    ctx = arc.import_report(header, _report_rows(f, header))
        if ctx is None:
            ctx = _existing_context(arc, context)
        before = arc.stats(ctx)
        out(json.dumps({"до": before["states"]}, ensure_ascii=False))
        refuted, failed = [], []
        for packet in values or []:
            try:
                arc.apply_example(ctx, packet)
            except ValueError as e:  # пакет не принят — дальше, с отчётом (архив откатывает транзакцию)
                failed.append((packet.get("key"), str(e)[:200]))
                continue
            for qid, payload in arc.db.execute(
                    "SELECT q.id, q.payload FROM refutations r JOIN examples e ON e.id = r.example "
                    "JOIN questions q ON q.id = r.question WHERE e.active = 1 AND e.name = ? AND q.context = ?",
                    (packet["key"], ctx)):
                p = json.loads(payload)
                refuted.append({"вопрос": " & ".join(p.get("запрет", [])), "вид": p.get("вид"), "строка": packet["key"]})
        after = arc.stats(ctx)
        out(json.dumps({"после": after["states"], "задания": after["pending"], "не принято пакетов": len(failed),
                        "примеры": failed[:3]}, ensure_ascii=False))
        for r in refuted:
            out(json.dumps(r, ensure_ascii=False))
        return before, after, refuted


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("архив")
    ap.add_argument("--выгрузка")
    ap.add_argument("--значения")
    ap.add_argument("--контекст", dest="context", help="точный ID контекста; обязателен при неоднозначном архиве без выгрузки")
    ap.add_argument("--строки-было", dest="rows_old", help="<схема>.rows.jsonl.gz прежних таблиц")
    ap.add_argument("--строки-стало", dest="rows_new", help="<схема>.rows.jsonl.gz новых таблиц")
    ap.add_argument("--источник", default="новые таблицы", help="reference для пакетов из строк")
    ap.add_argument("--переразметка", action="store_true", help="после значений: виды A/B/C по снимку --строки-стало")
    a = ap.parse_args(argv)
    values = json.load(open(a.значения, encoding="utf-8")) if a.значения else []
    if a.rows_old and a.rows_new:
        packets, added, conflicts = packets_from_rows(a.rows_old, a.rows_new, a.источник)
        lost = getattr(packets_from_rows, "lost", [])
        print(json.dumps({"строк с новыми значениями": len(packets), "новых значений": added,
                          "расхождений": len(conflicts), "примеры расхождений": conflicts[:5],
                          "строк с пропавшими значениями": len(lost), "примеры пропавших": lost[:5]}, ensure_ascii=False))
        values += packets
    _, after, _ = run(a.архив, a.выгрузка, values, context=a.context)
    if a.переразметка and a.rows_new:
        from collections import Counter
        with LiveArchive(a.архив) as arc:
            ctx = _existing_context(arc, after["context"])
            res = reclassify(arc, ctx, a.rows_new)
        moves = Counter((old, new) for old, new, _ in res.values())
        print(json.dumps({"переразметка": {f"{o}→{n}": c for (o, n), c in sorted(moves.items(), key=str)}},
                         ensure_ascii=False))
    return 0


if __name__ == "__main__":
    sys.exit(main())
