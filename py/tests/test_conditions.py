"""Сверка компактного хранения с прежним перебором, включая порядок."""

import unittest
from unittest.mock import patch

import numpy as np

from algen import enumerate as E
from algen.conditions import PackedConditions
from test_enumerate import RandomForm


class ConditionsTest(unittest.TestCase):
    def compare_paths(self, case, k=3):
        result = []
        for packed in (False, True):
            with patch.object(E, "PACKED_CONDITIONS", packed), patch.object(E, "VEC", case % 2 == 0):
                form = RandomForm(np.random.default_rng(case + 37), 6, 13,
                                  req=case % 3 == 1, need=case % 4 == 2)
                if case % 5 == 0:
                    form.fixed = [0]
                alive, empty = E.enumerate_form(form, k)
                result.append((list(alive.items()), list(E.minimal(alive).items()), empty, form.n_alive))
        self.assertEqual(result[0], result[1], f"случай {case}, k={k}")

    def test_old_and_packed_paths_match(self):
        for case in range(80):
            self.compare_paths(case, k=case % 5)

    def test_zeroes_order_lookup_and_sizes(self):
        s = PackedConditions(1024, 3, 30_753)
        rows = [(((0,), 0), 0), (((0,), 1023), 30_753),
                (((0, 0), 0), 2), (((0, 0, 0), 0), 1), (((), 0), 3)]
        for key, count in rows:
            s[key] = count
        self.assertEqual(list(s.items()), rows)
        self.assertEqual(len(s), len(rows))
        self.assertEqual(s[((0,), 1023)], 30_753)
        self.assertNotIn(((0,), 1), s)
        self.assertNotIn(((1024,), 0), s)
        self.assertEqual(s.nbytes, 10 * len(rows))
        # Нельзя молча обрезать большое значение или принять неупорядоченный блок.
        with self.assertRaises(ValueError):
            s[((0,), 0)] = 1
        with self.assertRaises(ValueError):
            s[((1,), 0)] = 30_754
        with self.assertRaises(OverflowError):
            PackedConditions(1 << 32, 3, 1)

    def test_uint_boundaries_and_duplicates(self):
        for count in (0, 255, 256, 65_535, 65_536, 2**32):
            s = PackedConditions(32, 4, count)
            s[((), 31)] = count
            s[((), 31)] = count
            self.assertEqual(list(s.items()), [(((), 31), count)])
            self.assertEqual(len(s), 1)

    def test_unsorted_goals_keep_dictionary_path(self):
        form = RandomForm(np.random.default_rng(9), 6, 13)
        with patch.object(E, "PACKED_CONDITIONS", True):
            alive, _ = E.enumerate_form(form, 3, goals=[8, 2, 8, 0])
        self.assertIsInstance(alive, dict)

    def test_negative_and_large_k_keep_old_path(self):
        for k in (-1, 64):
            form = RandomForm(np.random.default_rng(9), 6, 13)
            with patch.object(E, "PACKED_CONDITIONS", True):
                alive, _ = E.enumerate_form(form, k)
            self.assertIsInstance(alive, dict)
            self.compare_paths(9, k=k)

    def test_pair_filter_matches_dictionary(self):
        from types import SimpleNamespace
        # X ⇒ q; парная посылка X ∧ Y ⇒ q избыточна по половине X.
        m = np.zeros((3, 8), dtype=bool)
        for i, row in enumerate(((True, False, False, True),
                                 (True, True, True, True),
                                 (False, True, False, False))):
            for j, value in enumerate(row):
                m[i, 2 * j + (not value)] = True
        f = SimpleNamespace(m=m, fixed=[], pair_atoms={2: (0, 1)},
                            atoms=[("p", "p", "X"), ("p", "p", "Y"),
                                   ("pair", "p", "X", "Y", True), ("p", "q", "Z")])
        f.index = {a: i for i, a in enumerate(f.atoms)}
        rows = [(((0,), 6), 2), (((4,), 6), 1)]
        s = PackedConditions(8, 3, 3)
        for key, value in rows:
            s[key] = value
        self.assertEqual(list(E.pair_minimal(f, s).items()),
                         list(E.pair_minimal(f, dict(rows)).items()))
        self.assertEqual(len(E.pair_minimal(f, s)), 1)

    def test_generic_filter_matches_dictionary_with_class(self):
        import os
        from test_compress import GenForm, ZG
        for cls, clauses in (("", []), ("fin", []), ("fin", [[(("p", "fin", ZG), True)]])):
            with patch.dict(os.environ, {"ALGEN_CLASS": cls, "ALGEN_COMPRESS": ""}):
                f = GenForm([{"a": True, "b": True}], clauses=clauses)
                ia, ib = f.index[("p", "a", ZG)], f.index[("p", "b", ZG)]
                rows = [(((2 * ia,), 2 * ib), 1)]
                s = PackedConditions(2 * len(f.atoms), 3, 1)
                for key, value in rows:
                    s[key] = value
                want = list(E.generic_filter(f, dict(rows)).items())
                self.assertEqual(list(E.generic_filter(f, s).items()), want)

    def test_minimal_drops_supersets_without_materializing_dict(self):
        s = PackedConditions(8, 3, 10)
        s[((0,), 6)] = 2
        s[((0, 2), 6)] = 1
        s[((2, 4), 6)] = 3
        out = E.minimal(s)
        self.assertIsInstance(out, PackedConditions)
        self.assertEqual(list(out.items()), [(((0,), 6), 2), (((2, 4), 6), 3)])

    def test_comparison_catches_lost_or_changed_rows(self):
        original = PackedConditions.items

        def lose_first(store):
            it = original(store)
            next(it, None)
            yield from it

        def change_support(store):
            for key, count in original(store):
                yield key, count + 1

        for mutation in (lose_first, change_support):
            with patch.object(PackedConditions, "items", mutation):
                with self.assertRaises(AssertionError):
                    self.compare_paths(1)
