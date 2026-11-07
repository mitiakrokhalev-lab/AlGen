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

    def test_theory_const_unknown_in_rows(self):
        # c выводится из теории, но во второй строке его значение не выписано (ALGEN_FAST):
        # c — литерал-теорема, посылкой не перебирается, условие «c ⇒ ¬b» не выдаётся
        # (без c его опровергает третья строка — а c в ней на деле верно). Литерал,
        # ложный хоть в одной строке, решателю не отдаётся (строки — модели).
        from types import SimpleNamespace
        asked = []
        old = E.decide

        def fake(T, fixed, lit, s):
            asked.append(lit)
            return SimpleNamespace(kind="выводится" if lit == ("c", True) else "неизвестно")
        res = {}
        try:
            E.decide = fake
            for flag in (False, True):
                E.THEORY_CONST = flag
                form = FakeForm([(True, True, True), (False, True, None), (True, False, True)])
                form.sc = SimpleNamespace(T=None, s=None)
                form.lit = lambda j: ("abc"[j // 2], j % 2 == 0)
                alive, _ = enumerate_form(form, 2)
                res[flag] = (form.const, alive)
        finally:
            E.decide, E.THEORY_CONST = old, True
        self.assertEqual(res[False][0], [])
        self.assertEqual(res[True][0], [4])
        self.assertNotIn(("c", False), asked)
        self.assertNotIn(("a", True), asked)  # a ложно во второй строке
        self.assertTrue(all(4 not in prem for prem, _ in res[True][1]))
        self.assertTrue(any(4 in prem for prem, _ in res[False][1]))

    def test_theorem_satisfies_existence_requirement(self):
        # n = normal(H) (столбцы 0/1) — теорема, a — свойство G/H (требует столбец 0),
        # b — свойство G. n — литерал-теорема и посылкой не бывает; без REQ_CONST все
        # условия об a терялись (проверщик 5.11). С ним «b ⇒ a» и др. на месте.
        from types import SimpleNamespace
        rows = [(True, True, True), (None, True, True), (True, False, False)]
        old = E.decide
        E.decide = lambda T, fx, lit, s: SimpleNamespace(kind="выводится" if lit == ("n", True) else "неизвестно")
        res = {}
        try:
            for flag in (False, True):
                E.REQ_CONST = flag
                f = FakeForm(rows)
                f.req = {1: {0}}
                f.sc = SimpleNamespace(T=None, s=None)
                f.lit = lambda j: ("nab"[j // 2], j % 2 == 0)
                alive, _ = enumerate_form(f, 2)
                res[flag] = sorted((p, g) for p, g in alive if g // 2 == 1 or any(j // 2 == 1 for j in p))
        finally:
            E.decide, E.REQ_CONST = old, True
        self.assertEqual(res[False], [])
        self.assertEqual(res[True], [((2,), 4), ((3,), 5), ((4,), 2), ((5,), 3)])

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
    def test_early_min_keeps_all_conditions_counts_and_order(self):
        from unittest.mock import patch
        for case in range(80):
            rng = np.random.default_rng(700 + case)
            n, rows = int(rng.integers(4, 9)), int(rng.integers(0, 80))
            k = 3
            if case == 79:
                n, rows, k = 35, 7, 2  # >64 бит и неполный последний байт
            results = []
            for early, sparse in ((False, False), (True, False), (False, True), (True, True)):
                form = RandomForm(np.random.default_rng(800 + case), n, rows,
                                  req=case % 3 == 1, need=case % 4 == 2)
                if case % 7 == 0:
                    form.fixed = [0]
                if case % 5 == 0:
                    form.pair_atoms = {0: {1, 2}}
                if case % 11 == 0:
                    form.req = {1: {4}, 2: {2}}
                with patch.object(E, "EARLY_MIN", early), patch.object(E, "SPARSE_LEAF", sparse), patch.object(E, "VEC", True):
                    alive, empty = enumerate_form(form, k)
                if not form.fixed:
                    self.assertEqual(list(alive.items()), list(minimal(alive).items()))
                results.append((list(alive.items()), empty, form.n_alive))
            for result in results[1:]:
                self.assertEqual(results[0], result, msg=f"случай {case}")

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


class PackTest(unittest.TestCase):
    def test_pack_transposed_keeps_output(self):
        """pack по транспонированной матрице: те же условия, порядок, счётчик."""
        for case in range(60):
            rng = np.random.default_rng(300 + case)
            n, rows = int(rng.integers(4, 9)), int(rng.integers(3, 150))
            kw = dict(req=case % 3 == 1, need=case % 4 == 2)
            res = []
            for flag in (False, True):
                E.PACK_T = flag
                form = RandomForm(np.random.default_rng(300 + case), n, rows, **kw)
                alive, empty = enumerate_form(form, 3)
                res.append((list(alive.items()), empty, form.n_alive))
            E.PACK_T = True
            self.assertEqual(res[0], res[1], f"случай {case}")


class VCacheTest(unittest.TestCase):
    def test_cache_gives_same_verdicts_without_solver(self):
        """Второй прогон с кэшем вердиктов: те же вердикты и ядра, решатель не нужен;
        ключ не зависит от порядка посылок."""
        from types import SimpleNamespace
        calls = []
        old = E.decide

        def fake(T, prem, goal, s):
            calls.append((tuple(prem), goal))
            core = [prem[0]] if prem else []
            return SimpleNamespace(kind="выводится" if goal[1] else "неизвестно", core=core)
        a, b, c = ("p", "x", "G"), ("p", "y", "G"), ("p", "z", "G")
        qs = [([(a, True), (b, False)], (c, True)), ([(b, False)], (c, False)), ([], (a, True))]
        try:
            E.decide = fake
            E.VCACHE, E.VCACHE_OUT = None, {}
            first = [E.cdecide(None, p, g, None) for p, g in qs]
            n1 = len(calls)
            E.VCACHE, E.VCACHE_OUT = dict(E.VCACHE_OUT), {}
            second = [E.cdecide(None, list(reversed(p)), g, None) for p, g in qs]
        finally:
            E.decide, E.VCACHE, E.VCACHE_OUT = old, None, None
        self.assertEqual(n1, 3)
        self.assertEqual(len(calls), 3)  # второй прогон — без решателя
        self.assertEqual([v.kind for v in first], [v.kind for v in second])
        self.assertEqual([sorted(map(str, v.core)) for v in first], [sorted(map(str, v.core)) for v in second])


class JointTest(unittest.TestCase):
    def test_joint_matches_loop(self):
        """none_derivable / none_reduce: «да» только когда цикл decide не нашёл бы
        «выводится» ни для одного d (случайные теории, литералы-константы)."""
        import random
        from pysat.solvers import Solver
        from algen import fast
        from algen.logic import decide as slow

        class Th:
            def __init__(self, cl, nv, const):
                self.clauses, self.nv, self.const = cl, nv, const
                self.atoms = None

            def lit(self, a, v):
                c = self.const.get(a[1])
                if c is not None:
                    return None if c == v else False
                n = int(a[1][1:])
                return n if v else -n

            def solver(self):
                return Solver(name="g4", bootstrap_with=self.clauses)
        bad = checked = 0
        for case in range(150):
            rnd = random.Random(case)
            nv = rnd.randint(4, 12)
            cl = [[rnd.choice([1, -1]) * rnd.randint(1, nv) for _ in range(rnd.randint(1, 3))]
                  for _ in range(rnd.randint(2, 25))]
            const = {nv + 1: True, nv + 2: False} if case % 3 == 0 else {}
            th = Th(cl, nv, const)
            s = th.solver()
            fast._BANKS.pop(id(th), None)
            atoms = [("p", f"q{i}", "G") for i in list(range(1, nv + 1)) + list(const)]
            th.const = {f"q{i}": v for i, v in const.items()}
            for _ in range(15):
                prem = [(a, rnd.random() < 0.5) for a in rnd.sample(atoms, rnd.randint(0, 3))]
                ds = [(a, rnd.random() < 0.5) for a in rnd.sample(atoms, rnd.randint(2, 4))]
                goal = (rnd.choice(atoms), rnd.random() < 0.5)
                loop_d = any(slow(th, prem, d, s).kind == "выводится" for d in ds)
                if E.none_derivable(th, prem, ds, s):
                    checked += 1
                    bad += loop_d
                loop_r = any(slow(th, prem + [(a, not v)], (goal[0], not goal[1]), s).kind == "выводится"
                             for a, v in ds)
                if E.none_reduce(th, prem, goal, ds, s):
                    checked += 1
                    bad += loop_r
            fast._BANKS.pop(id(th), None)
            s.delete()
        self.assertEqual(bad, 0)
        self.assertGreater(checked, 100)
