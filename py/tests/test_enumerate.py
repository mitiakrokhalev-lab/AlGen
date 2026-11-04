"""Перебор условий: отсев по матрице библиотеки и минимальность.

    cd py && python3 -m unittest discover tests
"""

import unittest

import numpy as np

from algen import enumerate as E
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
        # Значение цели не записано: строка не опровергает. Без условий без посылок
        # (прежнее поведение) живы «a ⇒ c», «a ⇒ ¬c»; с ними — «⇒ c», «⇒ ¬c», а условия
        # с посылкой a неминимальны.
        E.ZERO_PREMISES = False
        try:
            form = FakeForm([(True, None, None)])
            alive, _ = enumerate_form(form, 1, goals=[4, 5])
            self.assertIn(((0,), 4), alive)
            self.assertIn(((0,), 5), alive)
        finally:
            E.ZERO_PREMISES = True
        form = FakeForm([(True, None, None)])
        alive, _ = enumerate_form(form, 1, goals=[4, 5])
        self.assertIn(((), 4), alive)
        self.assertIn(((), 5), alive)
        self.assertIn(((0,), 4), alive)  # не снимается: может оказаться доказуемым фактом

    def test_zero_premises(self):
        # c верно во всех строках: вопрос «всегда ли c?» — условие без посылок; «a ⇒ c»
        # остаётся (доказуемое — факт). ¬a опровергается первой строкой.
        form = FakeForm([(True, True, True), (False, True, True), (True, False, True)])
        alive, _ = enumerate_form(form, 2, goals=[1, 4])
        self.assertIn(((), 4), alive)
        self.assertNotIn(((), 1), alive)
        self.assertIn(((0,), 4), alive)

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


class VecTest(unittest.TestCase):
    def test_vector_leaf_keeps_output_and_order(self):
        """Лист векторами по целям: те же условия, тот же порядок, тот же счётчик."""
        import algen.enumerate as E
        for case in range(80):
            rng = np.random.default_rng(100 + case)
            n, rows = int(rng.integers(4, 9)), int(rng.integers(3, 60))
            kw = dict(req=case % 3 == 1, need=case % 4 == 2)
            res = []
            for vec in (False, True):
                E.VEC = vec
                form = RandomForm(np.random.default_rng(100 + case), n, rows, **kw)
                alive, empty = enumerate_form(form, 3)
                res.append((list(alive.items()), empty, form.n_alive))
            E.VEC = True
            self.assertEqual(res[0], res[1], f"случай {case}")


class BitsTest(unittest.TestCase):
    """Строки по битовым столбцам совпадают с прежней выборкой столбцов матрицы."""

    def test_rows_match_matrix(self):
        from algen.enumerate import Form
        rng = np.random.default_rng(3)
        for case in range(40):
            n, rows = int(rng.integers(3, 9)), int(rng.integers(1, 300))
            f = Form.__new__(Form)
            v = rng.integers(0, 3, size=(rows, n))
            m = np.zeros((rows, 2 * n), dtype=bool)
            for i in range(n):
                m[:, 2 * i], m[:, 2 * i + 1] = v[:, i] == 0, v[:, i] == 1
            f.m = f.s = m
            f.fixed = [0] if case % 3 == 0 else []
            synth = rng.random(rows) < 0.3
            f.synthetic = lambda r, synth=synth: bool(synth[r])
            for _ in range(20):
                k = int(rng.integers(1, 4))
                prem = sorted(rng.choice(2 * n, size=k, replace=False).tolist())
                g = int(rng.integers(0, 2 * n))
                neg = g ^ 1
                want = np.flatnonzero(m[:, prem + f.fixed + [neg]].all(axis=1))
                self.assertEqual(f.refuters(prem, g).tolist(), want.tolist())
                ur = np.flatnonzero(m[:, prem + f.fixed].all(axis=1) & ~m[:, g] & ~m[:, g ^ 1])
                self.assertEqual(f.unknown_rows(prem, g).tolist(), ur.tolist())
                cols = prem + f.fixed
                tr, fa = m[:, cols], m[:, [c ^ 1 for c in cols]]
                unk = ~tr & ~fa
                rr = np.flatnonzero(~fa.any(axis=1) & (unk.sum(axis=1) == 1))
                for limit in (None, 3):
                    r2 = rr
                    if limit is not None and len(r2) > limit:
                        r2 = np.concatenate([r2[~synth[r2]], r2[synth[r2]]])[:limit]
                    which = np.asarray(cols)[unk[r2].argmax(axis=1)] if len(r2) else []
                    self.assertEqual(f.one_unknown(prem, limit=limit),
                                     list(zip(r2.tolist(), [int(c) for c in which])))
