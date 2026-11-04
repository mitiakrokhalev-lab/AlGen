"""table.equiv_reps: дробление корзин моделями и банк дают те же классы, что
прежний перебор пар с logic.decide."""
import random
import unittest
from types import SimpleNamespace

import numpy as np
from pysat.solvers import Solver

from algen import fast, logic, table


class FakeT:
    """Теория: атом i → переменная (или None — верен всегда, False — ложен)."""

    def __init__(self, var, clauses):
        self.var, self.clauses = var, clauses

    def lit(self, a, v=True):
        x = self.var[a]
        if x is None:
            return None if v else False
        if x is False:
            return False if v else None
        return x if v else -x

    def solver(self):
        return Solver(name="g4", bootstrap_with=self.clauses)


def make(rnd):
    nv = rnd.randint(3, 9)
    cls = [[rnd.choice((1, -1)) * rnd.randint(1, nv) for _ in range(rnd.randint(1, 3))]
           for _ in range(rnd.randint(0, 2 * nv))]
    for _ in range(rnd.randint(0, 3)):  # равносильности x ↔ ±y
        x, y = rnd.sample(range(1, nv + 1), 2)
        y *= rnd.choice((1, -1))
        cls += [[-x, y], [x, -y]]
    natoms = rnd.randint(4, 14)
    var = [rnd.choice([None, False] + list(range(1, nv + 3))) if rnd.random() < 0.9 else rnd.randint(1, nv)
           for _ in range(natoms)]  # nv+1, nv+2 — свободные переменные (вне клауз)
    atoms = [("p", f"q{i}", None) for i in range(natoms)]
    T = FakeT({a: x for a, x in zip(atoms, var)}, cls)
    rows = rnd.randint(1, 3)
    m = np.zeros((rows, 2 * natoms), dtype=bool)  # мало строк: большие корзины
    for r in range(rows):
        for i in range(natoms):
            if rnd.random() < 0.2:
                m[r, 2 * i + rnd.randint(0, 1)] = True
    fixed = [2 * rnd.randrange(natoms) + rnd.randint(0, 1)] if rnd.random() < 0.3 else []

    def form():
        f = SimpleNamespace(m=m, atoms=atoms, fixed=fixed, sc=SimpleNamespace(T=T, s=T.solver()))
        f.lit = lambda j: (atoms[j // 2], j % 2 == 0)
        return f
    return form


class EquivTest(unittest.TestCase):
    def setUp(self):
        self.name, table.E.atom_name = table.E.atom_name, lambda a: a[1]

    def tearDown(self):
        table.E.atom_name = self.name
        fast._BANKS.clear()

    def test_same_classes_as_pairwise_logic_decide(self):
        rnd = random.Random(3)
        merged = 0
        for _ in range(300):
            form = make(rnd)
            old_n, table.EQUIV_MODELS = table.EQUIV_MODELS, 0
            try:
                want = table.equiv_reps(form(), decide=logic.decide)
            finally:
                table.EQUIV_MODELS = old_n
            fast._BANKS.clear()
            got = table.equiv_reps(form())
            self.assertEqual(got, want)
            merged += sum(r != j for j, r in enumerate(want))
        self.assertGreater(merged, 100)  # проверка не вырождена: классы есть


if __name__ == "__main__":
    unittest.main()
