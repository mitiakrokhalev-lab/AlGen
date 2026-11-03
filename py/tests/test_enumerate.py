"""Перебор условий: отсев по матрице библиотеки и минимальность.

    cd py && python3 -m unittest discover tests
"""

import unittest

import numpy as np

from algen.enumerate import clusters, cover, enumerate_form, minimal


class FakeForm:
    """Три атома a, b, c; строки — объекты библиотеки (верно / ложно / None)."""

    def __init__(self, rows):
        self.req, self.fixed = {}, []
        m = np.zeros((len(rows), 6), dtype=bool)
        for r, row in enumerate(rows):
            for i, v in enumerate(row):
                if v is not None:
                    m[r, 2 * i + (0 if v else 1)] = True
        self.e = self.m = m


class RandomForm:
    """Случайная таблица: n атомов, значения верно / ложно / неизвестно, условия
    существования req и покрытие need — как у формы схемы."""

    def __init__(self, rng, n, rows, req=False, need=False):
        v = rng.integers(0, 3, size=(rows, n))  # 0 — верно, 1 — ложно, 2 — неизвестно
        m = np.zeros((rows, 2 * n), dtype=bool)
        for i in range(n):
            m[:, 2 * i] = v[:, i] == 0
            m[:, 2 * i + 1] = v[:, i] == 1
        self.e = self.m = m
        self.fixed = []
        self.req = {}
        if req:
            for i in rng.choice(n, size=2, replace=False):
                self.req[int(i)] = {2 * int(rng.integers(0, n))}
        if need:
            self.need = [list(range(0, n // 2)), list(range(n // 2, n))]


class EnumerateTest(unittest.TestCase):
    def test_free_set_pruning_keeps_output(self):
        """Отсечение несвободных наборов посылок не меняет найденных условий."""
        import algen.enumerate as E
        rng = np.random.default_rng(7)
        for case in range(60):
            n, rows = int(rng.integers(4, 9)), int(rng.integers(3, 60))
            # мало строк и смещённые значения — много наборов с одинаковыми строками
            kw = dict(req=case % 3 == 1, need=case % 4 == 2)
            res = []
            for prune in (False, True):
                E.PRUNE_FREE = prune
                form = RandomForm(np.random.default_rng(case), n, rows, **kw)
                res.append(enumerate_form(form, 3)[0])
            E.PRUNE_FREE = True
            self.assertEqual(res[0], res[1], f"случай {case}")

    def test_refuted_and_minimal(self):
        # a ⇒ c на всех строках, b ⇒ c опровергается последней строкой.
        form = FakeForm([(True, True, True), (True, False, True), (False, True, False)])
        alive, empty = enumerate_form(form, 2, goals=[4])
        self.assertIn(((0,), 4), alive)
        self.assertNotIn(((2,), 4), alive)
        # a, b ⇒ c не минимально (хватает a): не хранится, но учтено в счётчике.
        self.assertNotIn(((0, 2), 4), alive)
        self.assertGreater(form.n_alive, len(alive))
        mins = minimal(alive)
        self.assertIn(((0,), 4), mins)
        self.assertNotIn(((0, 2), 4), mins)

    def test_unknown_value_does_not_refute(self):
        # Значение цели не записано: строка не опровергает.
        form = FakeForm([(True, None, None)])
        alive, _ = enumerate_form(form, 1, goals=[4, 5])
        self.assertIn(((0,), 4), alive)
        self.assertIn(((0,), 5), alive)

    def test_cover_prefers_shared_fact(self):
        # Условия 0 и 1 держатся на x или y, условие 2 — только на y:
        # хватает одного факта y.
        x, y, z = (frozenset([n]) for n in "xyz")
        out = cover([[x, y], [y, z], [y]])
        self.assertEqual(out, [y, y, y])

    def test_clusters_share_pair(self):
        ts = [("a", "b", "c"), ("a", "b", "d"), ("a", "b", "e"), ("c", "f", "g")]
        out = clusters(ts)
        self.assertEqual(out[0], (("a", "b"), ["c", "d", "e"]))
        self.assertEqual(len(out), 2)


if __name__ == "__main__":
    unittest.main()
