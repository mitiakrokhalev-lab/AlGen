"""Durable classification and update checks; Boolean fixtures, not groups."""
from collections import Counter
import json
from pathlib import Path
import sqlite3
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

import numpy as np

from algen import enumerate as E
from algen.conditions import PackedConditions
from algen.logic import App, Var
from algen.value_classify import ValueBudgetExceeded
from algen.value_ledger import ValueLedger, assignment, canonical, structure
from test_value_classify import fake, oracle, packed, queries_for


MANIFEST = dict(scheme="fixture", library="fixture-v1", theory="Boolean-only-fixture", language="fixture-v1")
SOURCE = dict(kind="user", reference="artificial Boolean fixture; not mathematical Library data")


def expected(form, conditions):
    queries = list(conditions)
    arrays = oracle(form, queries)
    result = []
    for i, q in enumerate(queries):
        a, b = map(int, arrays[4][i:i + 2])
        result.append((len(q[0]), conditions._encode(*q), *(int(x[i]) for x in arrays[:4]),
            tuple((int(r), int(c)) for r, c in zip(arrays[5][a:b], arrays[6][a:b]))))
    return result


def all_valid(form):
    queries = []
    for q in queries_for(sum(a[0] != 'pair' for a in form.atoms)):
        try:
            oracle(form, [q])
        except ValueError:
            continue
        queries.append(q)
    out = packed(form, queries)
    # Exercise the real block-order convention: zero premises last.
    out.blocks = {d: out.blocks[d] for d in (*sorted(set(out.blocks) - {0}), 0) if d in out.blocks}
    for n, (_, values) in out.blocks.items():
        for i in range(len(values)):
            values[i] = i % (out.max_support + 1)
    return out


class ValueLedgerTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="algen-ledger-test-")
        self.path = Path(self.tmp.name) / "values.sqlite"
        self.addCleanup(self.tmp.cleanup)

    def seed(self, form, conditions=None, **kw):
        conditions = conditions if conditions is not None else all_valid(form)
        ledger = ValueLedger.create(self.path, form, conditions,
            [dict(concrete=i) for i in range(len(form.m))], MANIFEST, SOURCE, batch_size=7, **kw)
        self.addCleanup(ledger.close)
        self.assertEqual(list(ledger.state_rows()), expected(form, conditions))
        self.assertEqual(list(ledger.conditions().items()), list(conditions.items()))
        return ledger, conditions

    def compare(self, ledger, form, conditions):
        self.assertEqual(list(ledger.state_rows()), expected(form, conditions))
        self.assertEqual(list(ledger.conditions().items()), list(conditions.items()))
        np.testing.assert_array_equal(ledger.projection().m, form.m)
        self.assertEqual(ledger.summary()['proof_pending'], len(conditions))
        self.assertFalse(ledger.summary()['candidate_frontier_complete'])
        self.assertFalse(ledger.summary()['current_support_computed'])

    def test_durable_updates_all_kinds_fixed_known_withdrawal_and_new_row(self):
        f = fake([(True, None, False), (None, None, True), (False, True, False)])
        f.fixed = [2]
        ledger, p = self.seed(f)
        saw = set(ledger.summary()['kinds'])
        for revision, (r, a, value) in enumerate([(0, 1, True), (0, 1, False),
                (0, 1, None), (1, 0, True), (2, 1, None), (1, 2, None)], 1):
            f.m[r, 2*a:2*a+2] = False
            if value is not None:
                f.m[r, 2*a + (not value)] = True
            receipt = ledger.apply_row(str(revision), dict(concrete=r), f.m[r], SOURCE, revision - 1)
            self.assertGreater(receipt['affected_conditions'], 0)
            self.compare(ledger, f, p)
            saw.update(ledger.summary()['kinds'])
        row = fake([(True, True, False)]).m[0]
        receipt = ledger.apply_row('new-row', dict(concrete=3), row, SOURCE, 6, add=True)
        self.assertEqual(receipt['affected_conditions'], len(p))
        f.m = np.vstack([f.m, row])
        self.compare(ledger, f, p)
        with ValueLedger(self.path) as other:
            self.compare(other, f, p)
            self.assertEqual(other.summary()['revision'], 7)
        self.assertEqual(saw, set('ABCR'))

    def test_opposite_polarities_share_observation_and_keep_exact_structures(self):
        f = fake([(None,)])
        ledger, p = self.seed(f, packed(f, [((), 0), ((), 1)]))
        hot = ledger.hot_values()
        self.assertEqual([(x['row'], x['atom'], x['want_true'], x['want_false']) for x in hot], [(0, 0, 1, 1)])
        identity = ledger.observation(0, 0)
        f.m[0, 0] = True
        ledger.apply_row('learn', dict(concrete=0), f.m[0], SOURCE, 0)
        self.assertEqual(identity, ledger.observation(0, 0))
        self.compare(ledger, f, p)
        self.assertNotEqual(structure(Var('center(G)')), structure(App('center', (Var('G'),))))
        self.assertNotEqual(structure(('obj', 1)), structure(['obj', 1]))
        self.assertNotEqual(structure(True), structure(1))
        self.assertEqual(assignment({Var('G'): ('obj', 'S3')}), assignment({Var('G'): ('obj', 'S3')}))

    def test_only_referencing_conditions_reclassified_even_when_previous_C_or_R(self):
        f = fake([(True, True, False)])
        ledger, p = self.seed(f, packed(f, [((), 0), ((), 1), ((), 2), ((), 3)]))
        f.m[0, :2] = False
        r = ledger.apply_row('withdraw', dict(concrete=0), f.m[0], SOURCE, 0)
        self.assertEqual(r['affected_conditions'], 2)
        self.compare(ledger, f, p)
        changed = [tuple(x) for x in ledger.db.execute('SELECT id,revision FROM conditions ORDER BY id')]
        self.assertEqual(changed, [(0, 1), (1, 1), (2, 0), (3, 0)])

    def test_pairs_and_fixed_expand_before_building_dependency_index(self):
        f = fake([(None, True, False)], [('p', 'p', 'A'), ('p', 'p', 'B'), ('p', 'q', 'G')])
        E.add_pairs(f, [('A', 'B')])
        p = packed(f, [((6,), 4), ((8,), 4), ((0,), 4)])
        ledger, _ = self.seed(f, p)
        f.m[0, 0] = True
        r = ledger.apply_row('pair-component', dict(concrete=0), f.m[0], SOURCE, 0)
        self.assertEqual(r['affected_conditions'], 3)
        self.compare(ledger, f, p)

    def test_replay_stale_writer_and_reused_event_key(self):
        f = fake([(None,)])
        ledger, p = self.seed(f)
        f.m[0, 0] = True
        r = ledger.apply_row('a', dict(concrete=0), f.m[0], SOURCE, 0)
        again = ledger.apply_row('a', dict(concrete=0), f.m[0], SOURCE, 0)
        self.assertEqual(again, dict(r, replayed=True))
        self.assertEqual(ledger.db.execute('SELECT count(*) FROM row_versions').fetchone()[0], 2)
        with self.assertRaisesRegex(ValueError, 'stale'):
            ledger.apply_row('b', dict(concrete=0), f.m[0], SOURCE, 0)
        with self.assertRaisesRegex(ValueError, 'different patch'):
            ledger.apply_row('a', dict(concrete=0), f.m[0], dict(SOURCE, reference='different'), 1)
        self.compare(ledger, f, p)

    def test_budget_failure_and_partial_write_roll_back_all_tables(self):
        f = fake([(True,)])
        ledger, p = self.seed(f, packed(f, [((), 0)]), max_events=0)
        before = list(ledger.state_rows())
        with self.assertRaises(ValueBudgetExceeded):
            ledger.apply_row('budget', dict(concrete=0), np.zeros(2, dtype=bool), SOURCE, 0)
        self.assertEqual(before, list(ledger.state_rows()))
        self.assertEqual(ledger.summary()['revision'], 0)
        self.assertEqual(ledger.db.execute('SELECT count(*) FROM changes').fetchone()[0], 0)
        original = ledger._reclassify
        def interrupt(*args):
            original(*args)
            raise KeyboardInterrupt('after numeric state writes')
        with patch.object(ledger, '_reclassify', interrupt), self.assertRaises(KeyboardInterrupt):
            ledger.apply_row('interrupt', dict(concrete=0), f.m[0], SOURCE, 0)
        self.compare(ledger, f, p)
        self.assertEqual(ledger.db.execute('SELECT count(*) FROM row_versions').fetchone()[0], 1)

    def test_process_crash_recovers_previous_generation(self):
        f = fake([(True,)])
        ledger, p = self.seed(f, packed(f, [((), 0)]))
        code = '''
import os,sys,numpy as np
from algen.value_ledger import ValueLedger
db=ValueLedger(sys.argv[1]); original=db._reclassify
def crash(*args):
 original(*args)
 os._exit(73)
db._reclassify=crash
db.apply_row('crash',dict(concrete=0),np.zeros(2,dtype=bool),dict(kind='user',reference='crash fixture'),0)
'''
        result = subprocess.run([sys.executable, '-B', '-c', code, str(self.path)], capture_output=True)
        self.assertEqual(result.returncode, 73, result.stderr.decode())
        with ValueLedger(self.path) as reopened:
            self.compare(reopened, f, p)
            self.assertEqual(reopened.summary()['revision'], 0)
            self.assertEqual(reopened.db.execute('SELECT count(*) FROM row_versions').fetchone()[0], 1)

    def test_incomplete_seed_disk_limit_duplicate_assignment_and_overwrite_rejected(self):
        f = fake([(None,)])
        with self.assertRaises(ValueBudgetExceeded):
            ValueLedger.create(self.path, f, packed(f, [((), 0)]), [dict(concrete=0)], MANIFEST, SOURCE, max_events=0)
        with self.assertRaisesRegex(ValueError, 'incomplete'):
            ValueLedger(self.path)
        with self.assertRaises(FileExistsError):
            ValueLedger.create(self.path, f, packed(f, [((), 0)]), [dict(concrete=0)], MANIFEST, SOURCE)
        f = fake([(True,)] * 100)
        path = self.path.with_name('disk.sqlite')
        with self.assertRaises(sqlite3.DatabaseError):
            ValueLedger.create(path, f, packed(f, [((), 0)]),
                [dict(concrete=i, large='x'*4096) for i in range(100)], MANIFEST, SOURCE, max_database_bytes=65536)
        duplicate = self.path.with_name('duplicate.sqlite')
        with self.assertRaises(sqlite3.IntegrityError):
            ValueLedger.create(duplicate, fake([(True,), (False,)]), packed(f, [((), 0)]),
                [dict(concrete=0)]*2, MANIFEST, SOURCE)


if __name__ == '__main__':
    unittest.main()
