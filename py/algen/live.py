"""Постоянная библиотека строк и динамический архив вопросов (SQLite).

Новая проверенная строка ищет опровержения через индекс атомов. Неизвестное
значение не опровергает. История строк и исходные вердикты сохраняются;
снятие источника возвращает зависимые вопросы. Новые минимальные условия
требуют полного перебора с кэшем — это явный долг, а не результат обновления.
"""

import argparse
from contextlib import contextmanager
import gzip
import hashlib
import json
import os
from pathlib import Path
import sqlite3
import zlib


VERSION = 1


def dumps(x):
    return json.dumps(x, ensure_ascii=False, sort_keys=True, separators=(",", ":"))


def digest(x):
    return hashlib.sha256(dumps(x).encode()).hexdigest()


def literal(s):
    if not isinstance(s, str) or not s or s == "¬":
        raise ValueError("литерал должен быть непустой строкой")
    return (s[1:], 0) if s.startswith("¬") else (s, 1)


def source_checked(source):
    # Это происхождение уже проверенных данных, а не проверка их математики.
    if (not isinstance(source, dict) or source.get("kind") not in ("library", "gap", "proof", "user")
            or not isinstance(source.get("reference"), str) or not source["reference"].strip()):
        raise ValueError("нужен источник library/gap/proof/user и reference; SAT-модель не пример группы")


def write_report(path, header, report, unconditional=()):
    """Атомарный потоковый экспорт ВСЕГО report, включая свёрнутые вопросы."""
    header = dict(header, format="algen.full-report", version=VERSION, complete=True)
    dst = Path(path)
    tmp = dst.with_name(dst.name + ".tmp")
    with gzip.open(tmp, "wt", encoding="utf-8") as f:
        f.write(dumps({"header": header}) + "\n")
        for row in report:
            f.write(dumps(row) + "\n")
        for goal in unconditional:
            forbidden = goal[1:] if goal.startswith("¬") else "¬" + goal
            f.write(dumps({"вердикт": "выводится", "посылки": [], "цель": goal, "ядро": [],
                           "запрет": [forbidden], "класс": [forbidden], "type": "unconditional"}) + "\n")
    os.replace(tmp, dst)


def export_matches(path, scheme, fingerprint):
    try:
        with gzip.open(path, "rt", encoding="utf-8") as f:
            h = json.loads(next(f))["header"]
        return (h.get("format") == "algen.full-report" and h.get("version") == VERSION
                and h.get("complete") is True and h.get("scheme") == scheme and h.get("library") == fingerprint)
    except (OSError, EOFError, StopIteration, KeyError, ValueError):
        return False


def library_row(form, row, reference):
    """Пакет из настоящей подстановки текущей Library, не из модели SAT.

    Берёт уже посчитанные значения матрицы; неизвестные остаются отсутствующими.
    Для исправления прежнего значения на неизвестное нужен явный null в patch.
    """
    from .enumerate import atom_name
    if not 0 <= row < len(form.envs):
        raise IndexError(row)
    assignment = {str(t): im for t, im in form.envs[row].items()}
    if not assignment:
        raise ValueError("нужна конкретная подстановка библиотеки")
    facts = {}
    for i, a in enumerate(form.atoms):
        if a[0] == "pair":
            continue
        yes, no = bool(form.m[row, 2 * i]), bool(form.m[row, 2 * i + 1])
        if yes and no:
            raise ValueError("строка одновременно утверждает и отрицает атом")
        if yes or no:
            facts[atom_name(a)] = yes
    return {"key": digest(assignment), "assignment": assignment, "facts": facts,
            "source": {"kind": "library", "reference": reference, "where": form.where(row)}}


class LiveArchive:
    def __init__(self, path):
        self.db = sqlite3.connect(path, isolation_level=None, timeout=60)
        self.db.row_factory = sqlite3.Row
        self.db.execute("PRAGMA foreign_keys=ON")
        self.db.execute("PRAGMA journal_mode=WAL")
        self.db.executescript("""
        CREATE TABLE IF NOT EXISTS meta(version INTEGER NOT NULL);
        INSERT INTO meta SELECT 1 WHERE NOT EXISTS(SELECT 1 FROM meta);
        CREATE TABLE IF NOT EXISTS contexts(
          id TEXT PRIMARY KEY, header TEXT NOT NULL, revision INTEGER NOT NULL DEFAULT 0);
        CREATE TABLE IF NOT EXISTS schemes(
          context TEXT REFERENCES contexts(id), name TEXT, complete INTEGER NOT NULL,
          PRIMARY KEY(context,name));
        CREATE TABLE IF NOT EXISTS records(
          context TEXT, scheme TEXT, position INTEGER, verdict TEXT NOT NULL, payload BLOB NOT NULL,
          PRIMARY KEY(context,scheme,position));
        CREATE TABLE IF NOT EXISTS questions(
          id TEXT PRIMARY KEY, context TEXT REFERENCES contexts(id), scheme TEXT NOT NULL,
          local TEXT NOT NULL, signature TEXT NOT NULL, verdict TEXT NOT NULL,
          payload TEXT NOT NULL, folded INTEGER NOT NULL, invalidated INTEGER NOT NULL DEFAULT 0,
          state TEXT NOT NULL, UNIQUE(context,scheme,local));
        CREATE INDEX IF NOT EXISTS questions_context ON questions(context,state);
        CREATE TABLE IF NOT EXISTS aliases(context TEXT, scheme TEXT, local TEXT,
          question TEXT REFERENCES questions(id), PRIMARY KEY(context,scheme,local));
        CREATE INDEX IF NOT EXISTS alias_question ON aliases(question,local);
        CREATE TABLE IF NOT EXISTS variants(
          id INTEGER PRIMARY KEY, question TEXT REFERENCES questions(id),
          formula TEXT NOT NULL, arity INTEGER NOT NULL, UNIQUE(question,formula));
        CREATE TABLE IF NOT EXISTS literals(
          context TEXT, atom TEXT, value INTEGER, variant INTEGER REFERENCES variants(id),
          PRIMARY KEY(variant,atom,value));
        CREATE INDEX IF NOT EXISTS literal_lookup ON literals(context,atom,value,variant);
        CREATE TABLE IF NOT EXISTS dependencies(
          child TEXT REFERENCES questions(id), parent TEXT REFERENCES questions(id),
          PRIMARY KEY(child,parent));
        CREATE INDEX IF NOT EXISTS dependent_lookup ON dependencies(parent,child);
        CREATE TABLE IF NOT EXISTS unresolved(child TEXT REFERENCES questions(id), reference TEXT,
          PRIMARY KEY(child,reference));
        CREATE TABLE IF NOT EXISTS examples(
          id INTEGER PRIMARY KEY, context TEXT REFERENCES contexts(id), name TEXT NOT NULL,
          revision INTEGER NOT NULL, assignment TEXT NOT NULL, source TEXT NOT NULL,
          active INTEGER NOT NULL, UNIQUE(context,name,revision));
        CREATE TABLE IF NOT EXISTS example_parents(
          child INTEGER REFERENCES examples(id), parent INTEGER REFERENCES examples(id),
          PRIMARY KEY(child,parent));
        CREATE TABLE IF NOT EXISTS example_hashes(
          example INTEGER PRIMARY KEY REFERENCES examples(id), content TEXT NOT NULL);
        CREATE UNIQUE INDEX IF NOT EXISTS active_example ON examples(context,name) WHERE active=1;
        CREATE TABLE IF NOT EXISTS facts(
          example INTEGER REFERENCES examples(id), atom TEXT, value INTEGER,
          PRIMARY KEY(example,atom));
        CREATE TABLE IF NOT EXISTS refutations(
          question TEXT REFERENCES questions(id), example INTEGER REFERENCES examples(id),
          variant INTEGER REFERENCES variants(id),
          PRIMARY KEY(question,example));
        CREATE TABLE IF NOT EXISTS jobs(
          context TEXT REFERENCES contexts(id), kind TEXT, revision INTEGER NOT NULL,
          PRIMARY KEY(context,kind));
        """)
        if self.db.execute("SELECT version FROM meta").fetchone()[0] != VERSION:
            self.close()
            raise ValueError("неподдерживаемая версия архива")
        self.db.execute("CREATE TEMP TABLE touched(id TEXT PRIMARY KEY)")

    def close(self):
        self.db.close()

    def __enter__(self):
        return self

    def __exit__(self, *args):
        self.close()

    @contextmanager
    def transaction(self):
        self.db.execute("BEGIN IMMEDIATE")
        try:
            yield
            self.db.execute("COMMIT")
        except BaseException:
            self.db.execute("ROLLBACK")
            raise

    def _context(self, header):
        required = ("base", "class", "theory", "library", "declaration")
        if any(k not in header or not isinstance(header[k], str) for k in required):
            raise ValueError("неполный контекст: нужны base/class/theory/library/declaration")
        if not header["base"] or not header["theory"] or not header["library"]:
            raise ValueError("пустой отпечаток контекста")
        fixed = header.get("fixed", [])
        if not isinstance(fixed, list):
            raise ValueError("fixed должен быть списком литералов")
        for item in fixed:
            literal(item)
        variables = header.get("variables", [])
        if not isinstance(variables, list) or any(not isinstance(v, str) or not v for v in variables):
            raise ValueError("variables должен быть списком имён переменных")
        identity = dict({k: header[k] for k in required}, fixed=sorted(set(fixed)), variables=sorted(set(variables)))
        ctx = digest(identity)
        self.db.execute("INSERT OR IGNORE INTO contexts(id,header) VALUES(?,?)", (ctx, dumps(identity)))
        return ctx

    def import_report(self, header, rows):
        """Одна атомарная схема. Новая теория/библиотека — отдельный снимок.

        Повторный импорт схемы отвергается: он не должен молча затирать историю.
        """
        if not isinstance(header.get("scheme"), str) or not header["scheme"]:
            raise ValueError("нет имени схемы")
        complete = (header.get("format") == "algen.full-report" and header.get("version") == VERSION
                    and header.get("complete") is True)
        with self.transaction():
            self.db.execute("DELETE FROM touched")
            ctx = self._context(header)
            sid = header["scheme"]
            self.db.execute("INSERT INTO schemes VALUES(?,?,?)", (ctx, sid, int(complete)))
            fixed = header.get("fixed", [])
            if not isinstance(fixed, list):
                raise ValueError("fixed должен быть списком литералов")
            for position, row in enumerate(rows):
                self.db.execute("INSERT INTO records VALUES(?,?,?,?,?)",
                                (ctx, sid, position, str(row.get("вердикт", "")), zlib.compress(dumps(row).encode(), 3)))
                verdict = row.get("вердикт")
                if verdict not in ("неизвестно", "выводится"):
                    continue
                formula = sorted(set(row["запрет"]) | set(fixed))
                if not formula:
                    raise ValueError("пустой запрет")
                signature = dumps(row.get("класс", formula))
                local = str(row.get("№") or digest(signature))
                qid = digest([ctx, sid, signature])
                folded = bool(row.get("свёрнута")) and verdict == "неизвестно"
                previous = self.db.execute("SELECT q.id,q.signature,q.verdict FROM aliases a JOIN questions q ON q.id=a.question "
                                           "WHERE a.context=? AND a.scheme=? AND a.local=?",
                                           (ctx, sid, local)).fetchone()
                same_class = self.db.execute("SELECT verdict FROM questions WHERE id=?", (qid,)).fetchone()
                if same_class and same_class[0] != verdict:
                    raise ValueError("разные вердикты одного класса")
                if previous and (previous["signature"] != signature or previous["verdict"] != verdict):
                    raise ValueError("коллизия номера/разные вердикты класса: " + local)
                self.db.execute("INSERT OR IGNORE INTO questions(id,context,scheme,local,signature,verdict,payload,folded,state) "
                                "VALUES(?,?,?,?,?,?,?,?,?)", (qid, ctx, sid, local, signature, verdict, dumps(row), int(folded),
                                                               "folded" if folded else ("open" if verdict == "неизвестно" else "proved")))
                self.db.execute("INSERT OR IGNORE INTO aliases VALUES(?,?,?,?)", (ctx, sid, local, qid))
                self.db.execute("INSERT OR IGNORE INTO touched VALUES(?)", (qid,))
                self.db.execute("INSERT OR IGNORE INTO variants(question,formula,arity) VALUES(?,?,?)", (qid, dumps(formula), len(formula)))
                vid = self.db.execute("SELECT id FROM variants WHERE question=? AND formula=?", (qid, dumps(formula))).fetchone()[0]
                self.db.executemany("INSERT OR IGNORE INTO literals VALUES(?,?,?,?)",
                                    ((ctx, *literal(s), vid) for s in formula))
                if folded:
                    refs = row.get("следует из", [])
                    for ref in refs or ["нет источников"]:
                        self.db.execute("INSERT OR IGNORE INTO unresolved VALUES(?,?)", (qid, str(ref)))
            # Связи могут идти к строкам, встретившимся позже в потоке.
            for dep in self.db.execute("SELECT u.child,u.reference,q.scheme FROM unresolved u JOIN questions q ON q.id=u.child "
                                       "WHERE q.context=?", (ctx,)).fetchall():
                ref = dep["reference"]
                target_sid, target_local = (ref.rsplit(":", 1) if ":" in ref and not ref.startswith("экземпляр:")
                                            else (dep["scheme"], ref))
                parent = self.db.execute("SELECT q.id FROM aliases a JOIN questions q ON q.id=a.question "
                                         "WHERE a.context=? AND a.scheme=? AND a.local=? AND q.verdict='неизвестно'",
                                         (ctx, target_sid, target_local)).fetchone()
                if parent:
                    self.db.execute("INSERT OR IGNORE INTO dependencies VALUES(?,?)", (dep["child"], parent[0]))
                    self.db.execute("DELETE FROM unresolved WHERE child=? AND reference=?", (dep["child"], ref))
            # Неразрешённая внешняя ссылка не даёт права скрыть вопрос.
            self.db.execute("UPDATE questions SET invalidated=1,state='open' WHERE context=? AND verdict='неизвестно' "
                            "AND id IN(SELECT child FROM unresolved)", (ctx,))
            self._check_cycles(ctx)
            # Новая схема должна сразу увидеть уже записанные примеры снимка.
            for ex in self.db.execute("SELECT id FROM examples WHERE context=? AND active=1", (ctx,)).fetchall():
                self._match(ex[0], ctx)
            self._refresh(ctx)
            if self.db.execute("SELECT 1 FROM questions WHERE context=? AND invalidated=1 LIMIT 1", (ctx,)).fetchone():
                self._schedule(ctx, "compress")
            return ctx

    def _check_cycles(self, ctx):
        # Kahn в SQLite: межсхемный граф не материализуется Python-словарём.
        self.db.execute("CREATE TEMP TABLE IF NOT EXISTS topo(id TEXT PRIMARY KEY, degree INTEGER)")
        self.db.execute("CREATE INDEX IF NOT EXISTS topo_degree ON topo(degree)")
        self.db.execute("CREATE TEMP TABLE IF NOT EXISTS roots(id TEXT PRIMARY KEY)")
        self.db.execute("DELETE FROM topo")
        self.db.execute("INSERT INTO topo SELECT d.child,0 FROM dependencies d JOIN questions q ON q.id=d.child WHERE q.context=? "
                        "UNION SELECT d.parent,0 FROM dependencies d JOIN questions q ON q.id=d.child WHERE q.context=?", (ctx, ctx))
        self.db.execute("UPDATE topo SET degree=(SELECT count(*) FROM dependencies d WHERE d.child=topo.id)")
        while True:
            self.db.execute("DELETE FROM roots")
            self.db.execute("INSERT INTO roots SELECT id FROM topo WHERE degree=0")
            if not self.db.execute("SELECT 1 FROM roots LIMIT 1").fetchone():
                break
            self.db.execute("UPDATE topo SET degree=degree-(SELECT count(*) FROM dependencies d JOIN roots r ON r.id=d.parent WHERE d.child=topo.id) "
                            "WHERE id IN(SELECT d.child FROM dependencies d JOIN roots r ON r.id=d.parent)")
            self.db.execute("DELETE FROM topo WHERE id IN(SELECT id FROM roots)")
        if self.db.execute("SELECT 1 FROM topo LIMIT 1").fetchone():
            raise ValueError("цикл зависимостей сжатия")

    def import_file(self, path):
        opener = gzip.open if str(path).endswith(".gz") else open
        with opener(path, "rt", encoding="utf-8") as f:
            header = json.loads(next(f))["header"]
            return self.import_report(header, (json.loads(s) for s in f if s.strip()))

    def _match(self, eid, ctx):
        """Только варианты, имеющие хотя бы один известный литерал этой строки.

        Индекс по атому даёт кандидатов; NOT EXISTS требует ВСЕ литералы одного
        варианта (а не смешивает разные подстановки или симметричные варианты).
        """
        sql = """SELECT DISTINCT v.question,v.id FROM facts f
          JOIN literals l INDEXED BY literal_lookup ON l.context=? AND l.atom=f.atom AND l.value=f.value
          JOIN variants v ON v.id=l.variant
          WHERE f.example=? AND NOT EXISTS(
            SELECT 1 FROM literals missing WHERE missing.variant=v.id AND NOT EXISTS(
              SELECT 1 FROM facts known WHERE known.example=? AND known.atom=missing.atom AND known.value=missing.value))"""
        candidates = self.db.execute(sql, (ctx, eid, eid))
        for qid, vid in candidates:
            kind = self.db.execute("SELECT verdict FROM questions WHERE id=?", (qid,)).fetchone()[0]
            if kind == "выводится":
                raise ValueError("пример противоречит доказанному факту: " + qid)
            self.db.execute("INSERT OR IGNORE INTO refutations VALUES(?,?,?)", (qid, eid, vid))
            self.db.execute("INSERT OR IGNORE INTO touched VALUES(?)", (qid,))

    def _refresh(self, ctx):
        self.db.execute("CREATE TEMP TABLE IF NOT EXISTS changed(id TEXT PRIMARY KEY)")
        self.db.execute("DELETE FROM changed")
        self.db.execute("INSERT INTO changed SELECT q.id FROM touched t JOIN questions q ON q.id=t.id "
                        "WHERE q.context=? AND q.verdict='неизвестно' AND "
                        "((q.state='refuted') != EXISTS(SELECT 1 FROM refutations r JOIN examples e ON e.id=r.example "
                        "WHERE r.question=q.id AND e.active=1))", (ctx,))
        # Новый child может ссылаться на уже опровергнутый/раскрытый parent.
        self.db.execute("INSERT OR IGNORE INTO changed SELECT d.parent FROM dependencies d JOIN questions p ON p.id=d.parent "
                        "JOIN touched t ON t.id=d.child WHERE p.context=? AND (p.state='refuted' OR p.invalidated=1)", (ctx,))
        # Любое изменение ответа источника делает старую свёртку неактуальной.
        self.db.execute("CREATE TEMP TABLE IF NOT EXISTS impacted(id TEXT PRIMARY KEY)")
        self.db.execute("DELETE FROM impacted")
        self.db.execute("""WITH RECURSIVE walk(id) AS(
          SELECT d.child FROM dependencies d JOIN changed c ON c.id=d.parent
          UNION SELECT d.child FROM dependencies d JOIN walk i ON i.id=d.parent)
          INSERT INTO impacted SELECT id FROM walk""")
        self.db.execute("UPDATE questions SET invalidated=1 WHERE id IN(SELECT id FROM impacted)")
        self.db.execute("INSERT OR IGNORE INTO touched SELECT id FROM impacted")
        self.db.execute("""UPDATE questions SET state=CASE
          WHEN EXISTS(SELECT 1 FROM refutations r JOIN examples e ON e.id=r.example
                      WHERE r.question=questions.id AND e.active=1) THEN 'refuted'
          WHEN folded=1 AND invalidated=0 THEN 'folded' ELSE 'open' END
          WHERE id IN(SELECT id FROM touched) AND context=? AND verdict='неизвестно'""", (ctx,))

    def _dirty(self, ctx):
        self.db.execute("UPDATE contexts SET revision=revision+1 WHERE id=?", (ctx,))
        revision = self.db.execute("SELECT revision FROM contexts WHERE id=?", (ctx,)).fetchone()[0]
        for kind in ("enumerate", "compress"):
            self._schedule(ctx, kind)
        return revision

    def _schedule(self, ctx, kind):
        revision = self.db.execute("SELECT revision FROM contexts WHERE id=?", (ctx,)).fetchone()[0]
        self.db.execute("INSERT INTO jobs VALUES(?,?,?) ON CONFLICT(context,kind) DO UPDATE SET revision=excluded.revision",
                        (ctx, kind, revision))

    def apply_example(self, ctx, packet, replace=False):
        """Добавить знания о КОНКРЕТНОЙ подстановке. null отзывается явно.

        Разные строки не объединяются в контрпример. Исправления bool требуют
        replace=True; прежняя версия остаётся в истории. Источник обязателен.
        """
        source_checked(packet.get("source"))
        key, assignment, patch = packet["key"], packet["assignment"], packet["facts"]
        if not isinstance(key, str) or not key or not isinstance(assignment, dict) or not assignment:
            raise ValueError("нужны key и конкретная assignment")
        if not isinstance(patch, dict) or any(not isinstance(a, str) or not a or a.startswith("¬") or
                                              (v is not None and type(v) is not bool) for a, v in patch.items()):
            raise ValueError("facts: атом → bool или null; 0/1 не принимаются вместо bool")
        with self.transaction():
            self.db.execute("DELETE FROM touched")
            if not self.db.execute("SELECT 1 FROM contexts WHERE id=?", (ctx,)).fetchone():
                raise ValueError("неизвестный контекст")
            h = json.loads(self.db.execute("SELECT header FROM contexts WHERE id=?", (ctx,)).fetchone()[0])
            if h["variables"] and set(assignment) != set(h["variables"]):
                raise ValueError("подстановка не покрывает переменные базы")
            previous = self.db.execute("SELECT * FROM examples WHERE context=? AND name=? AND active=1", (ctx, key)).fetchone()
            facts = dict(self.db.execute("SELECT atom,value FROM facts WHERE example=?", (previous["id"],))) if previous else {}
            if previous and previous["assignment"] != dumps(assignment):
                raise ValueError("ключ относится к другой подстановке")
            old = dict(facts)
            if replace:
                facts = {}
            for atom, val in patch.items():
                if val is None:
                    facts.pop(atom, None)
                else:
                    if atom in facts and facts[atom] != val and not replace:
                        raise ValueError("исправление значения требует replace=True: " + atom)
                    facts[atom] = int(val)
            if previous and old == facts and previous["source"] == dumps(packet["source"]):
                return self.stats(ctx)
            revision = self._dirty(ctx)
            if previous:
                self.db.execute("INSERT OR IGNORE INTO touched SELECT question FROM refutations WHERE example=?", (previous["id"],))
                self.db.execute("UPDATE examples SET active=0 WHERE id=?", (previous["id"],))
            eid = self.db.execute("INSERT INTO examples(context,name,revision,assignment,source,active) VALUES(?,?,?,?,?,1)",
                                  (ctx, key, revision, dumps(assignment), dumps(packet["source"]))).lastrowid
            if previous:
                self.db.execute("INSERT INTO example_parents VALUES(?,?)", (eid, previous["id"]))
            self.db.executemany("INSERT INTO facts VALUES(?,?,?)", ((eid, a, v) for a, v in facts.items()))
            self.db.execute("INSERT INTO example_hashes VALUES(?,?)", (eid, digest([assignment, packet["source"], facts])))
            self._match(eid, ctx)
            self._refresh(ctx)
            return self.stats(ctx)

    def withdraw(self, ctx, key, source):
        source_checked(source)
        with self.transaction():
            self.db.execute("DELETE FROM touched")
            old = self.db.execute("SELECT * FROM examples WHERE context=? AND name=? AND active=1", (ctx, key)).fetchone()
            if old is None:
                raise ValueError("нет активной строки")
            revision = self._dirty(ctx)
            self.db.execute("INSERT OR IGNORE INTO touched SELECT question FROM refutations WHERE example=?", (old["id"],))
            self.db.execute("UPDATE examples SET active=0 WHERE id=?", (old["id"],))
            # Пустая неактивная версия хранит причину отзыва.
            eid = self.db.execute("INSERT INTO examples(context,name,revision,assignment,source,active) VALUES(?,?,?,?,?,0)",
                                  (ctx, key, revision, old["assignment"], dumps(source))).lastrowid
            self.db.execute("INSERT INTO example_parents VALUES(?,?)", (eid, old["id"]))
            self._refresh(ctx)
            return self.stats(ctx)

    def stats(self, ctx):
        states = dict(self.db.execute("SELECT state,count(*) FROM questions WHERE context=? GROUP BY state", (ctx,)))
        revision = self.db.execute("SELECT revision FROM contexts WHERE id=?", (ctx,)).fetchone()
        if revision is None:
            raise ValueError("неизвестный контекст")
        return {"context": ctx, "revision": revision[0], "states": states,
                "record_verdicts": dict(self.db.execute("SELECT verdict,count(*) FROM records WHERE context=? GROUP BY verdict", (ctx,))),
                "schemes": dict(self.db.execute("SELECT complete,count(*) FROM schemes WHERE context=? GROUP BY complete", (ctx,))),
                "examples": self.db.execute("SELECT count(*) FROM examples WHERE context=? AND active=1", (ctx,)).fetchone()[0],
                "invalidated": self.db.execute("SELECT count(*) FROM questions WHERE context=? AND invalidated=1", (ctx,)).fetchone()[0],
                "unresolved": self.db.execute("SELECT count(*) FROM unresolved u JOIN questions q ON q.id=u.child WHERE q.context=?", (ctx,)).fetchone()[0],
                "pending": [dict(r) for r in self.db.execute("SELECT kind,revision FROM jobs WHERE context=? ORDER BY kind", (ctx,))]}

    def questions(self, ctx, state=None):
        sql = "SELECT id,state,payload FROM questions WHERE context=?"
        args = [ctx]
        if state:
            sql += " AND state=?"
            args.append(state)
        for r in self.db.execute(sql + " ORDER BY id", args):
            yield dict(json.loads(r["payload"]), archive_id=r["id"], archive_state=r["state"],
                       aliases=[a[0] for a in self.db.execute("SELECT local FROM aliases WHERE question=? ORDER BY local", (r["id"],))],
                       counterexamples=self.evidence(r["id"]))

    def evidence(self, qid):
        return [{"key": r["name"], "revision": r["revision"], "assignment": json.loads(r["assignment"]),
                 "source": json.loads(r["source"]), "source_history": self.source_history(r["id"]),
                 "forbidden": json.loads(r["formula"])}
                for r in self.db.execute("SELECT e.*,v.formula FROM refutations r JOIN examples e ON e.id=r.example "
                                         "JOIN variants v ON v.id=r.variant WHERE r.question=? AND e.active=1 ORDER BY e.id", (qid,))]

    def source_history(self, eid):
        return [dict(r, source=json.loads(r["source"])) for r in self.db.execute("""WITH RECURSIVE history(id) AS(
          SELECT ? UNION SELECT p.parent FROM example_parents p JOIN history h ON h.id=p.child)
          SELECT e.id,e.revision,e.source FROM examples e JOIN history h ON h.id=e.id ORDER BY e.id""", (eid,))]

    def records(self, ctx, scheme):
        for (payload,) in self.db.execute("SELECT payload FROM records WHERE context=? AND scheme=? ORDER BY position", (ctx, scheme)):
            yield json.loads(zlib.decompress(payload))

    def active_examples(self, ctx):
        for r in self.db.execute("SELECT * FROM examples WHERE context=? AND active=1 ORDER BY id", (ctx,)):
            yield {"id": r["id"], "key": r["name"], "revision": r["revision"],
                   "assignment": json.loads(r["assignment"]), "source": json.loads(r["source"]),
                   "facts": {a: bool(v) for a, v in self.db.execute("SELECT atom,value FROM facts WHERE example=?", (r["id"],))}}

    def fingerprint(self, ctx):
        h = hashlib.sha256(ctx.encode())
        for name, content in self.db.execute("SELECT e.name,h.content FROM examples e JOIN example_hashes h ON h.example=e.id "
                                             "WHERE e.context=? AND e.active=1 ORDER BY e.name", (ctx,)):
            h.update(dumps([name, content]).encode() + b"\0")
        return h.hexdigest()

    def carry_examples(self, source, target):
        """Перенести действующие строки в новый снимок той же теории/области.

        По одной атомарной строке, повтор безопасен. Старый снимок и история
        остаются; изменённая теория требует отдельной проверки данных.
        """
        headers = []
        for ctx in (source, target):
            r = self.db.execute("SELECT header FROM contexts WHERE id=?", (ctx,)).fetchone()
            if r is None:
                raise ValueError("неизвестный контекст")
            h = json.loads(r[0])
            h.pop("library")
            headers.append(h)
        if headers[0] != headers[1]:
            raise ValueError("разные теория или область: перенос требует перепроверки")
        if source == target:
            return self.stats(target)
        for p in self.active_examples(source):
            original_id = p.pop("id")
            p.pop("revision")
            p["source"] = dict(p["source"], parent_context=source, parent_example=original_id)
            self.apply_example(target, p)
            with self.transaction():
                child = self.db.execute("SELECT id FROM examples WHERE context=? AND name=? AND active=1", (target, p["key"])).fetchone()[0]
                self.db.execute("INSERT OR IGNORE INTO example_parents VALUES(?,?)", (child, original_id))
        return self.stats(target)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("db")
    sub = ap.add_subparsers(dest="command", required=True)
    p = sub.add_parser("import")
    p.add_argument("files", nargs="+")
    p = sub.add_parser("status")
    p.add_argument("context", nargs="?")
    p = sub.add_parser("add-example")
    p.add_argument("context")
    p.add_argument("packet")
    p.add_argument("--replace", action="store_true")
    p = sub.add_parser("withdraw")
    p.add_argument("context")
    p.add_argument("key")
    p.add_argument("source")
    p = sub.add_parser("export")
    p.add_argument("context")
    p.add_argument("--state")
    p = sub.add_parser("records")
    p.add_argument("context")
    p.add_argument("scheme")
    p = sub.add_parser("carry")
    p.add_argument("source")
    p.add_argument("target")
    args = ap.parse_args()
    with LiveArchive(args.db) as a:
        if args.command == "import":
            for f in args.files:
                ctx = a.import_file(f)
                print(dumps(a.stats(ctx)))
        elif args.command == "status":
            ids = [args.context] if args.context else [r[0] for r in a.db.execute("SELECT id FROM contexts ORDER BY id")]
            for ctx in ids:
                print(dumps(a.stats(ctx)))
        elif args.command == "add-example":
            print(dumps(a.apply_example(args.context, json.loads(Path(args.packet).read_text()), args.replace)))
        elif args.command == "withdraw":
            print(dumps(a.withdraw(args.context, args.key, json.loads(Path(args.source).read_text()))))
        elif args.command == "records":
            for row in a.records(args.context, args.scheme):
                print(dumps(row))
        elif args.command == "carry":
            print(dumps(a.carry_examples(args.source, args.target)))
        else:
            for row in a.questions(args.context, args.state):
                print(dumps(row))


if __name__ == "__main__":
    main()
