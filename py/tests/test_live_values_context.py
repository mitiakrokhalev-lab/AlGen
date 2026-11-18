"""Synthetic context isolation, exact replay and rollback; no new group facts."""
import contextlib
import gzip
import io
import json
import tempfile
import unittest
from pathlib import Path

from algen.live import LiveArchive, context_identity, digest, write_report
from tools.live_values import main, run


HEADER = dict(base='G', **{'class': ''}, scheme='S', theory='T', library='L',
              declaration='forall G', variables=['G'], fixed=[])


def row(atom, number='1'):
    return {'вердикт': 'неизвестно', 'запрет': [atom], 'класс': [atom], '№': number, 'вид': 'A'}


class LiveValuesContextTest(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='algen-live-context-')
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.db = self.root/'archive.db'

    def export(self, name, header=HEADER, rows=None):
        path = self.root/name
        write_report(path, header, rows if rows is not None else [row('a(G)')])
        return path

    def packet(self):
        return dict(key='g0', assignment={'G': 'g0'}, facts={'a(G)': True, 'b(G)': True},
                    source=dict(kind='user', reference='synthetic test assumptions'))

    def quiet(self, export=None, values=None, **kw):
        return run(self.db, export, values, out=lambda *_: None, **kw)

    def contents(self):
        with LiveArchive(self.db) as arc:
            return list(arc.db.iterdump())

    def rewrite(self, path, header, rows):
        with gzip.open(path, 'wt', encoding='utf-8') as stream:
            stream.write(json.dumps({'header': header})+'\n')
            for value in rows:
                stream.write((value if isinstance(value, str) else json.dumps(value))+'\n')

    def assert_new_context(self, field, value):
        old = self.export('old.gz')
        old_ctx = self.quiet(old)[1]['context']
        new = self.export('new.gz', dict(HEADER, **{field: value}), [row('b(G)')])
        after = self.quiet(new, [self.packet()])[1]
        self.assertNotEqual(after['context'], old_ctx)
        self.assertEqual(after['states'], {'refuted': 1})
        with LiveArchive(self.db) as arc:
            self.assertEqual(arc.stats(old_ctx)['states'], {'open': 1})
            self.assertEqual(arc.db.execute('SELECT count(*) FROM contexts').fetchone()[0], 2)
            self.assertEqual(arc.db.execute('SELECT count(*) FROM examples WHERE context=?', (old_ctx,)).fetchone()[0], 0)

    def test_changed_theory_same_scheme_never_updates_old_context(self):
        self.assert_new_context('theory', 'new-T')

    def test_changed_library_same_scheme_never_updates_old_context(self):
        self.assert_new_context('library', 'new-L')

    def test_identity_is_pure_and_matches_independent_v1_fixture(self):
        h = dict(HEADER, fixed=['q(G)', 'p(G)', 'p(G)'], variables=['H', 'G', 'G'])
        self.assertEqual(digest(context_identity(h)), '8e97113817baf9c6fe98a32ad60bdfc9eb51e5b392ea8fe73fdbdf4a1054ac9b')
        self.assertEqual(context_identity(h)['variables'], ['G', 'H'])
        self.assertFalse(self.db.exists())

    def test_identical_export_and_value_replay_preserves_history(self):
        p = self.export('same.gz')
        self.quiet(p, [self.packet()])
        before = self.contents()
        self.quiet(p, [self.packet()])
        self.assertEqual(before, self.contents())

    def test_explicit_context_conflicting_with_export_rejected_before_update(self):
        old_ctx = self.quiet(self.export('old.gz'))[1]['context']
        before = self.contents()
        p = self.export('new.gz', dict(HEADER, theory='new-T'))
        with self.assertRaisesRegex(ValueError, 'не совпадает'):
            self.quiet(p, [self.packet()], context=old_ctx)
        self.assertEqual(before, self.contents())

    def test_missing_or_ambiguous_context_never_chooses_first(self):
        with self.assertRaisesRegex(ValueError, 'единственного'):
            self.quiet(values=[self.packet()])
        self.quiet(self.export('one.gz'))
        self.quiet(self.export('two.gz', dict(HEADER, theory='new-T')))
        before = self.contents()
        with self.assertRaisesRegex(ValueError, 'единственного'):
            self.quiet(values=[self.packet()])
        self.assertEqual(before, self.contents())

    def test_explicit_context_selects_one_of_multiple_and_unknown_fails(self):
        first = self.quiet(self.export('one.gz'))[1]['context']
        second = self.quiet(self.export('two.gz', dict(HEADER, theory='new-T')))[1]['context']
        self.quiet(values=[self.packet()], context=second)
        with LiveArchive(self.db) as arc:
            self.assertEqual(arc.stats(first)['states'], {'open': 1})
            self.assertEqual(arc.stats(second)['states'], {'refuted': 1})
        before = self.contents()
        with self.assertRaisesRegex(ValueError, 'неизвестный'):
            self.quiet(values=[self.packet()], context='absent')
        self.assertEqual(before, self.contents())

    def test_changed_export_header_is_rejected_without_erasing_original(self):
        p = self.export('original.gz')
        self.quiet(p)
        before = self.contents()
        p = self.export('changed.gz', dict(HEADER, generation={'k': 2}))
        with self.assertRaisesRegex(ValueError, 'выгрузка изменилась'):
            self.quiet(p, [self.packet()])
        self.assertEqual(before, self.contents())

    def test_changed_missing_extra_reordered_or_malformed_records_rejected(self):
        p = self.export('original.gz', rows=[row('a(G)'), row('b(G)', '2')])
        self.quiet(p)
        with gzip.open(p, 'rt') as stream:
            header = json.loads(next(stream))['header']
        before = self.contents()
        for rows in ([row('b(G)', '2'), row('a(G)')], [row('a(G)')],
                     [row('a(G)'), row('b(G)', '2'), row('c(G)', '3')],
                     [row('a(G)'), row('changed(G)', '2')], [row('a(G)'), '{broken']):
            with self.subTest(rows=rows):
                changed = self.root/'changed.gz'
                self.rewrite(changed, header, rows)
                with self.assertRaises(ValueError):
                    self.quiet(changed, [self.packet()])
                self.assertEqual(before, self.contents())

    def test_truncated_first_import_rolls_back_entire_new_snapshot(self):
        before = self.contents()
        p = self.export('truncated.gz', rows=[row('a(G)'), row('b(G)', '2')])
        with gzip.open(p, 'rt') as stream:
            header = json.loads(next(stream))['header']
        self.rewrite(p, header, [row('a(G)')])
        with self.assertRaisesRegex(ValueError, 'обрезана'):
            self.quiet(p, [self.packet()])
        self.assertEqual(before, self.contents())

    def test_incomplete_or_invalid_counters_cannot_claim_full_import(self):
        before = self.contents()
        p = self.export('bad.gz')
        with gzip.open(p, 'rt') as stream:
            good = json.loads(next(stream))['header']
        for patch in ({'complete': False}, {'version': True}, {'report_count': True},
                      {'unconditional_count': -1}, {'report_count': None}):
            self.rewrite(p, dict(good, **patch), [row('a(G)')])
            with self.subTest(patch=patch), self.assertRaises(ValueError):
                self.quiet(p, [self.packet()])
            self.assertEqual(before, self.contents())

    def test_cli_reclassifies_selected_export_context_not_first_context(self):
        old_ctx = self.quiet(self.export('old.gz'))[1]['context']
        new = self.export('new.gz', dict(HEADER, theory='new-T'), [row('b(G)')])
        rows = self.root/'rows.gz'
        with gzip.open(rows, 'wt') as stream:
            stream.write(json.dumps({'атомы': ['a(G)', 'b(G)']})+'\n')
            stream.write(json.dumps({'t': [0], 'f': [1]})+'\n')
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            self.assertEqual(main([str(self.db), '--выгрузка', str(new), '--строки-стало',
                                   str(rows), '--переразметка']), 0)
        self.assertEqual(json.loads(output.getvalue().splitlines()[-1]), {'переразметка': {'A→C': 1}})
        with LiveArchive(self.db) as arc:
            self.assertEqual(arc.stats(old_ctx)['states'], {'open': 1})


if __name__ == '__main__':
    unittest.main()
