"""Experimental durable value queue for ONE frozen PackedConditions domain.

The stored input supports and proof-pending states are not a fresh report.
Row replacements must be independently checked complete projections; this
module does not derive facts, retract their mathematical descendants, merge
assignments across schemes, or discover newly minimal conditions. Those debts
remain explicit. Numeric classification uses the existing bounded C++ API.
"""

from contextlib import contextmanager
import hashlib
import json
import os
from pathlib import Path
import sqlite3
from types import SimpleNamespace

import numpy as np

from .conditions import PackedConditions
from .live import source_checked
from .logic import App, Var
from .value_classify import KINDS, PreparedValues, ValueBudgetExceeded, library


def canonical(value):
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"), allow_nan=False)


def structure(value):
    """Typed, exact identity; no pretty names, repr, or guessed object aliases."""
    if isinstance(value, Var):
        return ["var", value.name]
    if isinstance(value, App):
        return ["app", value.op, [structure(x) for x in value.args]]
    if isinstance(value, tuple):
        return ["tuple", [structure(x) for x in value]]
    if isinstance(value, list):
        return ["list", [structure(x) for x in value]]
    if isinstance(value, dict):
        if any(type(k) is not str for k in value):
            raise ValueError("identity dictionaries require string keys")
        return ["dict", [[k, structure(v)] for k, v in sorted(value.items())]]
    if value is None or type(value) in (str, int, bool):
        return [type(value).__name__, value]
    raise ValueError("unsupported structural identity type: " + type(value).__name__)


def _unstructure(value):
    kind, *args = value
    if kind == "var":
        return Var(args[0])
    if kind == "app":
        return App(args[0], tuple(_unstructure(x) for x in args[1]))
    if kind in ("tuple", "list"):
        result = [_unstructure(x) for x in args[0]]
        return tuple(result) if kind == "tuple" else result
    if kind == "dict":
        return {k: _unstructure(v) for k, v in args[0]}
    if kind not in ("str", "int", "bool", "NoneType"):
        raise ValueError("invalid stored structural identity")
    return args[0]


def assignment(env):
    """Exact concrete images attached to structural variable descriptors."""
    return sorted([[structure(v), structure(im)] for v, im in env.items()], key=canonical)


class ValueLedger:
    VERSION = 1

    def _open(self, path, maximum):
        self.path = Path(path)
        self.db = sqlite3.connect(path, isolation_level=None, timeout=30)
        self.db.row_factory = sqlite3.Row
        self.db.execute("PRAGMA foreign_keys=ON")
        self.db.execute("PRAGMA journal_mode=DELETE")
        self.db.execute("PRAGMA synchronous=FULL")
        self.db.execute("PRAGMA cache_size=-2048")
        page = self.db.execute("PRAGMA page_size").fetchone()[0]
        if type(maximum) is not int or maximum < 65536:
            raise ValueError("database budget must be at least 64KiB")
        self.db.execute("PRAGMA max_page_count=" + str(maximum // page))
        self.db.execute("CREATE TEMP TABLE affected(id INTEGER PRIMARY KEY)")

    def __init__(self, path):
        if not Path(path).is_file():
            raise FileNotFoundError(path)
        # Apply the stored bound again: SQLite's page-count setting is per connection.
        self._open(path, 65536)
        try:
            if self._meta("version") != self.VERSION or not self._meta("complete"):
                raise ValueError("incomplete or incompatible value ledger")
            maximum = self._meta("max_database_bytes")
            page = self.db.execute("PRAGMA page_size").fetchone()[0]
            self.db.execute("PRAGMA max_page_count=" + str(maximum // page))
        except BaseException:
            self.close()
            raise

    @classmethod
    def create(cls, path, form, conditions, row_identities, manifest, source, *,
               max_database_bytes=64 * 1024**2, max_matrix_bytes=128 * 1024**2,
               batch_size=4096, max_events=262144):
        """Atomic seed. Failed files remain explicitly incomplete; never overwrite."""
        if not isinstance(conditions, PackedConditions):
            raise ValueError("ledger seed requires PackedConditions")
        if form.m.dtype != np.dtype(bool) or form.m.ndim != 2:
            raise ValueError("Boolean matrix required")
        if (type(max_matrix_bytes) is not int or max_matrix_bytes < 1
                or form.m.nbytes > max_matrix_bytes):
            raise ValueError("projection exceeds matrix budget")
        if type(batch_size) is not int or batch_size < 1 or type(max_events) is not int or max_events < 0:
            raise ValueError("invalid numeric batch budget")
        if (not isinstance(manifest, dict) or any(not isinstance(manifest.get(k), str)
                or not manifest[k] for k in ("scheme", "library", "theory", "language"))):
            raise ValueError("manifest requires scheme/library/theory/language versions")
        source_checked(source)
        snapshot = SimpleNamespace(atoms=tuple(form.atoms), fixed=tuple(form.fixed),
            pair_atoms={i: set(v) for i, v in getattr(form, "pair_atoms", {}).items()}, m=form.m.copy())
        prepared = PreparedValues(snapshot)
        if conditions.literals != prepared.ncols:
            raise ValueError("condition vocabulary differs from projection")
        handle = os.open(path, os.O_CREAT | os.O_EXCL | os.O_WRONLY, 0o600)
        os.close(handle)
        out = cls.__new__(cls)
        try:
            out._open(path, max_database_bytes)
            out.db.executescript("""
            CREATE TABLE meta(key TEXT PRIMARY KEY, value TEXT NOT NULL);
            CREATE TABLE rows(id INTEGER PRIMARY KEY, identity TEXT NOT NULL UNIQUE, revision INTEGER NOT NULL);
            CREATE TABLE row_versions(row_id INTEGER REFERENCES rows(id), revision INTEGER,
              projection BLOB NOT NULL, source TEXT NOT NULL, PRIMARY KEY(row_id,revision));
            CREATE TABLE conditions(id INTEGER PRIMARY KEY, depth INTEGER NOT NULL,
              code BLOB NOT NULL, original_support TEXT NOT NULL, kind INTEGER NOT NULL,
              single INTEGER NOT NULL, multi INTEGER NOT NULL, refuting INTEGER NOT NULL,
              revision INTEGER NOT NULL, UNIQUE(depth,code));
            CREATE TABLE literals(condition_id INTEGER REFERENCES conditions(id), atom INTEGER,
              wanted INTEGER NOT NULL, PRIMARY KEY(condition_id,atom));
            CREATE INDEX literal_lookup ON literals(atom,condition_id);
            CREATE TABLE events(condition_id INTEGER REFERENCES conditions(id), row_id INTEGER REFERENCES rows(id),
              wanted INTEGER NOT NULL, PRIMARY KEY(condition_id,row_id));
            CREATE TABLE changes(event TEXT PRIMARY KEY, packet TEXT NOT NULL, receipt TEXT NOT NULL);
            """)
            out._put("version", cls.VERSION)
            out._put("complete", False)
            with out._atomic():
                metadata = dict(manifest=manifest, atoms=[structure(a) for a in snapshot.atoms],
                    pairs={str(i): sorted(v) for i, v in snapshot.pair_atoms.items()}, fixed=list(snapshot.fixed),
                    width=conditions.width, max_premises=conditions.max_premises,
                    max_support=conditions.max_support, block_order=list(conditions.blocks),
                    ncols=prepared.ncols, max_database_bytes=max_database_bytes,
                    max_matrix_bytes=max_matrix_bytes, batch_size=batch_size, max_events=max_events,
                    projection_sha256=prepared.context_sha256, revision=0)
                for k, v in metadata.items():
                    out._put(k, v)
                seen = 0
                for r, identity in enumerate(row_identities):
                    if r >= prepared.nrows:
                        raise ValueError("too many row identities")
                    out.db.execute("INSERT INTO rows VALUES(?,?,0)", (r, canonical(structure(identity))))
                    out.db.execute("INSERT INTO row_versions VALUES(?,0,?,?)",
                        (r, out._pack(snapshot.m[r]), canonical(source)))
                    seen += 1
                if seen != prepared.nrows:
                    raise ValueError("row identities do not cover the projection")
                domain = hashlib.sha256()
                count = 0
                for b in prepared.iter_batches(conditions, batch_size=batch_size, max_events=max_events):
                    supports = conditions.blocks[b.depth][1]
                    for i, code in enumerate(b.keys):
                        code = int(code)
                        support = int(supports[b.start + i])
                        out.db.execute("INSERT INTO conditions VALUES(?,?,?,?,?,?,?,?,0)",
                            (count, b.depth, code.to_bytes(8, "big"), str(support), int(b.kinds[i]),
                             int(b.single[i]), int(b.multi[i]), int(b.refuting[i])))
                        forbidden = out._forbidden(code, b.depth, conditions.width, prepared)
                        out.db.executemany("INSERT INTO literals VALUES(?,?,?)",
                            ((count, c // 2, c) for c in forbidden))
                        out._events(count, b, i)
                        domain.update((canonical([b.depth, code, support]) + "\n").encode())
                        count += 1
                if count != len(conditions):
                    raise ValueError("incomplete condition seed")
                out._put("conditions", count)
                out._put("domain_sha256", domain.hexdigest())
                out._put("engine_sha256", library().source_hash)
                out._put("complete", True)
            return out
        except BaseException:
            if hasattr(out, "db"):
                out.close()
            raise

    def _meta(self, key):
        r = self.db.execute("SELECT value FROM meta WHERE key=?", (key,)).fetchone()
        if r is None:
            raise ValueError("missing ledger metadata: " + key)
        return json.loads(r[0])

    def _put(self, key, value):
        self.db.execute("INSERT OR REPLACE INTO meta VALUES(?,?)", (key, canonical(value)))

    @contextmanager
    def _atomic(self):
        self.db.execute("BEGIN IMMEDIATE")
        try:
            yield
            self.db.execute("COMMIT")
        except BaseException:
            if self.db.in_transaction:
                self.db.execute("ROLLBACK")
            raise

    def close(self):
        self.db.close()

    @contextmanager
    def read(self):
        """Consistent multi-query read, also nestable inside an update transaction."""
        nested = self.db.in_transaction
        if not nested:
            self.db.execute("BEGIN")
        try:
            yield self
        finally:
            if not nested and self.db.in_transaction:
                self.db.execute("ROLLBACK")

    def __enter__(self):
        return self

    def __exit__(self, *exc):
        self.close()

    @staticmethod
    def _pack(row):
        return np.packbits(row, bitorder="little").tobytes()

    @staticmethod
    def _forbidden(code, depth, width, prepared):
        mask = (1 << width) - 1
        goal = code & mask
        code >>= width
        columns = [goal ^ 1, *prepared.fixed]
        for _ in range(depth):
            columns.append(code & mask)
            code >>= width
        return sorted({c for j in columns for c in prepared.expansions[int(j)]})

    def _events(self, condition, batch, i):
        start, end = map(int, batch.offsets[i:i + 2])
        self.db.executemany("INSERT INTO events VALUES(?,?,?)",
            ((condition, int(batch.rows[j]), int(batch.columns[j])) for j in range(start, end)))

    def projection(self):
        """Caller must use a read transaction when sharing the DB with a writer."""
        ncols = self._meta("ncols")
        rows = self.db.execute("SELECT count(*) FROM rows").fetchone()[0]
        if rows * ncols > self._meta("max_matrix_bytes"):
            raise ValueError("projection exceeds matrix budget")
        m = np.empty((rows, ncols), dtype=bool)
        for expected, rec in enumerate(self.db.execute("SELECT r.id,v.projection FROM rows r JOIN row_versions v "
                "ON v.row_id=r.id AND v.revision=r.revision ORDER BY r.id")):
            if rec["id"] != expected or len(rec["projection"]) != (ncols + 7) // 8:
                raise ValueError("incomplete stored row projection")
            m[expected] = np.unpackbits(np.frombuffer(rec["projection"], dtype='u1'), bitorder="little")[:ncols]
        return SimpleNamespace(m=m, atoms=[_unstructure(a) for a in self._meta("atoms")],
            fixed=self._meta("fixed"), pair_atoms={int(k): set(v) for k, v in self._meta("pairs").items()})

    def conditions(self):
        out = PackedConditions(self._meta("ncols"), self._meta("max_premises"), self._meta("max_support"))
        for rec in self.db.execute("SELECT depth,code,original_support FROM conditions ORDER BY id"):
            depth, code = rec["depth"], int.from_bytes(rec["code"], "big")
            goal, prem = code & out.mask, []
            code >>= out.width
            for _ in range(depth):
                prem.append(code & out.mask)
                code >>= out.width
            out[tuple(reversed(prem)), goal] = int(rec["original_support"])
        return out

    def state_rows(self):
        with self.read():
            for rec in self.db.execute("SELECT * FROM conditions ORDER BY id"):
                one = tuple(tuple(r) for r in self.db.execute(
                    "SELECT row_id,wanted FROM events WHERE condition_id=? ORDER BY row_id", (rec["id"],)))
                yield (rec["depth"], int.from_bytes(rec["code"], "big"), rec["kind"],
                       rec["single"], rec["multi"], rec["refuting"], one)

    def summary(self):
        with self.read():
            kinds = {KINDS[k]: n for k, n in self.db.execute("SELECT kind,count(*) FROM conditions GROUP BY kind")}
            return dict(revision=self._meta("revision"), conditions=self._meta("conditions"), kinds=kinds,
                rows=self.db.execute("SELECT count(*) FROM rows").fetchone()[0],
                proof_pending=self._meta("conditions"), domain_import_complete=self._meta("complete"),
                candidate_frontier_complete=False, source_propagation_complete=False,
                current_support_computed=False, original_support_preserved=True,
                database_bytes=self.path.stat().st_size)

    def observation(self, row, atom):
        atoms = self._meta("atoms")
        if not 0 <= atom < len(atoms) or _unstructure(atoms[atom])[0] == "pair":
            raise ValueError("observation requires a primitive atom")
        rec = self.db.execute("SELECT identity FROM rows WHERE id=?", (row,)).fetchone()
        if rec is None:
            raise ValueError("unknown assignment")
        return dict(manifest=self._meta("manifest"), assignment=json.loads(rec[0]), atom=atoms[atom])

    def hot_values(self, limit=20):
        if type(limit) is not int or not 1 <= limit <= 1000:
            raise ValueError("hot-value limit must be 1..1000")
        with self.read():
            result = []
            for row, atom, yes, no in self.db.execute("SELECT e.row_id,e.wanted/2,"
                    "sum(e.wanted%2=0),sum(e.wanted%2=1) FROM events e JOIN conditions c ON c.id=e.condition_id "
                    "WHERE c.kind=1 GROUP BY e.row_id,e.wanted/2 ORDER BY count(*) DESC,e.row_id,e.wanted/2 LIMIT ?", (limit,)):
                result.append(dict(row=row, atom=atom, want_true=yes, want_false=no,
                                   observation=self.observation(row, atom)))
            return result

    def _reclassify(self, prepared, revision):
        """Bounded reads/writes; the affected set lives in SQLite, not a Python set."""
        cursor = self.db.execute("SELECT c.id,c.depth,c.code FROM conditions c JOIN affected a ON a.id=c.id ORDER BY c.id")
        pending = cursor.fetchmany(self._meta("batch_size"))
        while pending:
            start = 0
            while start < len(pending):
                depth = pending[start]["depth"]
                end = start + 1
                while end < len(pending) and pending[end]["depth"] == depth:
                    end += 1
                size = end - start
                while True:
                    keys = np.array([int.from_bytes(x["code"], "big") for x in pending[start:start + size]], dtype='u8')
                    try:
                        b = prepared.classify(keys, depth, self._meta("width"), max_events=self._meta("max_events"))
                        break
                    except ValueBudgetExceeded:
                        if size == 1:
                            raise
                        size = max(1, size // 2)
                for i, old in enumerate(pending[start:start + size]):
                    cid = old["id"]
                    self.db.execute("UPDATE conditions SET kind=?,single=?,multi=?,refuting=?,revision=? WHERE id=?",
                        (int(b.kinds[i]), int(b.single[i]), int(b.multi[i]), int(b.refuting[i]), revision, cid))
                    self.db.execute("DELETE FROM events WHERE condition_id=?", (cid,))
                    self._events(cid, b, i)
                start += size
            pending = cursor.fetchmany(self._meta("batch_size"))

    def apply_row(self, event, identity, row, source, expected_revision, *, add=False):
        """Replace one complete checked projection; retry event keys idempotently.

        This is NOT a proof checker or a source-withdrawal engine. New rules,
        language, source dependency closures, and unseen candidates stay debts.
        """
        source_checked(source)
        if not isinstance(event, str) or not event or type(expected_revision) is not int or type(add) is not bool:
            raise ValueError("event key, expected revision and add flag required")
        row = np.asarray(row)
        ncols = self._meta("ncols")
        if row.dtype != np.dtype(bool) or row.shape != (ncols,):
            raise ValueError("complete Boolean row projection required")
        atoms = [_unstructure(a) for a in self._meta("atoms")]
        primitive = [i for i, a in enumerate(atoms) if a[0] != "pair"]
        if any(row[2*i] and row[2*i+1] for i in primitive):
            raise ValueError("contradictory primitive row")
        packed, key = self._pack(row), canonical(structure(identity))
        packet = canonical(dict(add=add, identity=key, row=packed.hex(), source=source))
        with self._atomic():
            previous = self.db.execute("SELECT packet,receipt FROM changes WHERE event=?", (event,)).fetchone()
            if previous:
                if previous[0] != packet:
                    raise ValueError("event key reused for a different patch")
                return dict(json.loads(previous[1]), replayed=True)
            revision = self._meta("revision")
            if expected_revision != revision:
                raise ValueError("stale ledger revision")
            current = self.db.execute("SELECT r.id,r.revision,v.projection FROM rows r JOIN row_versions v "
                "ON v.row_id=r.id AND v.revision=r.revision WHERE identity=?", (key,)).fetchone()
            if (current is None) != add:
                raise ValueError("assignment already exists" if add else "unknown assignment")
            revision += 1
            self.db.execute("DELETE FROM affected")
            if add:
                rid = self.db.execute("SELECT count(*) FROM rows").fetchone()[0]
                if (rid + 1) * ncols > self._meta("max_matrix_bytes"):
                    raise ValueError("new row exceeds matrix budget")
                self.db.execute("INSERT INTO rows VALUES(?,?,?)", (rid, key, revision))
                self.db.execute("INSERT INTO affected SELECT id FROM conditions")
            else:
                rid = current["id"]
                old = np.unpackbits(np.frombuffer(current["projection"], dtype='u1'), bitorder="little")[:ncols]
                for a in primitive:
                    if np.any(old[2*a:2*a+2] != row[2*a:2*a+2]):
                        self.db.execute("INSERT OR IGNORE INTO affected SELECT condition_id FROM literals WHERE atom=?", (a,))
                self.db.execute("UPDATE rows SET revision=? WHERE id=?", (revision, rid))
            self.db.execute("INSERT INTO row_versions VALUES(?,?,?,?)", (rid, revision, packed, canonical(source)))
            prepared = PreparedValues(self.projection())
            if library().source_hash != self._meta("engine_sha256"):
                raise ValueError("numeric classifier changed; explicit full refresh required")
            affected = self.db.execute("SELECT count(*) FROM affected").fetchone()[0]
            self._reclassify(prepared, revision)
            self._put("revision", revision)
            receipt = dict(event=event, revision=revision, row=rid, affected_conditions=affected,
                all_conditions=self._meta("conditions"), add=add, projection_sha256=prepared.context_sha256,
                proof_pending=self._meta("conditions"), candidate_frontier_complete=False,
                source_propagation_complete=False, current_support_computed=False)
            self.db.execute("INSERT INTO changes VALUES(?,?,?)", (event, packet, canonical(receipt)))
            return receipt
