"""library.backbone: тот же ответ, что у двух вызовов решателя на литерал."""
import random
import unittest

from pysat.solvers import Solver

from algen.library import backbone


def two_calls(s, assume, lits):
    out = []
    for l in lits:
        if not s.solve(assumptions=assume + [-l]):
            out.append(True)
        elif not s.solve(assumptions=assume + [l]):
            out.append(False)
        else:
            out.append(None)
    return out


class BackboneTest(unittest.TestCase):
    def test_same_as_two_calls(self):
        rnd = random.Random(7)
        cases = 0
        for _ in range(400):
            n = rnd.randint(3, 14)
            cls = [[rnd.choice((1, -1)) * rnd.randint(1, n) for _ in range(rnd.randint(1, 3))]
                   for _ in range(rnd.randint(1, 3 * n))]
            assume = [rnd.choice((1, -1)) * v for v in rnd.sample(range(1, n + 1), rnd.randint(0, 3))]
            lits = [rnd.choice((1, -1)) * rnd.randint(1, n + 2) for _ in range(rnd.randint(1, 2 * n))]
            with Solver(name="g4", bootstrap_with=cls) as a, Solver(name="g4", bootstrap_with=cls) as b:
                want = two_calls(a, assume, lits)
                self.assertEqual(backbone(b, assume, lits), want, (cls, assume, lits))
                cases += any(v is not None for v in want) and None in want
        self.assertGreater(cases, 50)  # проверка не вырождена: есть и выведенные, и неизвестные


if __name__ == "__main__":
    unittest.main()
