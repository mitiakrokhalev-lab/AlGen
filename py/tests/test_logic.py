"""Вывод на SAT выводит учебное, не выводит ложного и отдаёт ядро посылок.

    cd py && python3 -m unittest discover tests
"""

import unittest

from algen.logic import Graph, Theory, Vocab, decide


def p(prop, t, value=True):
    return ("p", prop, t), value


class Extension(unittest.TestCase):
    """Схема G, N ◁ G, G/N."""

    @classmethod
    def setUpClass(cls):
        g = Graph(Vocab.section("grp"))
        cls.G = g.var("G", "Grp.obj")
        cls.N = g.var("N", "Grp.sub", ambient=cls.G)
        cls.Q = g.given(g.make("quotient", [cls.G, cls.N]))
        cls.T = Theory(g, grow=1)
        cls.s = cls.T.solver()

    def decide(self, prem, goal):
        return decide(self.T, prem, goal, self.s)

    def test_closure_under_extensions(self):
        for prop in ("finite", "solvable", "fin-gen", "periodic"):
            v = self.decide([p("normal", self.N), p(prop, self.N), p(prop, self.Q)], p(prop, self.G))
            self.assertEqual(v.kind, "выводится", prop)

    def test_nilpotent_is_not_closed_under_extensions(self):
        # S₃: N = A₃ и S₃/A₃ абелевы, S₃ не нильпотентна.
        v = self.decide([p("normal", self.N), p("nilpotent", self.N), p("nilpotent", self.Q)],
                        p("nilpotent", self.G))
        self.assertEqual(v.kind, "неизвестно")

    def test_core_drops_redundant_premise(self):
        # Нормальная максимальная подгруппа имеет простой индекс: ф. а. G не нужна.
        prem = [p("residually-finite", self.G), p("normal", self.N), p("maximal", self.N)]
        v = self.decide(prem, p("finite-index", self.N))
        self.assertEqual(v.kind, "выводится")
        self.assertNotIn(p("residually-finite", self.G), v.core)

    def test_contradiction(self):
        # Простая группа с нормальной подгруппой, не тривиальной и не всей.
        v = self.decide([p("simple", self.G), p("normal", self.N), p("trivial", self.N, False),
                         p("whole", self.N, False)], p("abelian", self.G))
        self.assertEqual(v.kind, "противоречие")

    def test_no_group_is_forced(self):
        for prop in ("finite", "trivial", "abelian", "nilpotent"):
            for value in (True, False):
                self.assertTrue(self.s.solve(assumptions=[self.T.lit(("p", prop, self.G), value)]),
                                (prop, value))


if __name__ == "__main__":
    unittest.main()
