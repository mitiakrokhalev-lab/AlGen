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


class SameObject(unittest.TestCase):
    """Соглашение 6.11.2026: идемпотентность и «внутренний автоморфизм» — только у
    отображения X → X (один объект). Кэли, X → X̂, проекция — ложно всегда; вложение
    N → X — ⇔ N = X; у F: X → Y — влечёт X ≅ Y."""

    @classmethod
    def setUpClass(cls):
        g = Graph(Vocab.section("grp"))
        cls.G = g.var("G", "Grp.obj")
        cls.H = g.var("H", "Grp.obj")
        cls.N = g.var("N", "Grp.sub", ambient=cls.G)
        cls.Z = g.given(g.make("center", [cls.G]))
        cls.cay = g.given(g.make("cayley", [cls.G]))
        cls.pro = g.given(g.make("profinite-map", [cls.G]))
        cls.inc = g.given(g.make("incl", [cls.G, cls.Z]))
        cls.F = g.var("F", "Grp.mor", dom=cls.G, cod=cls.H)
        cls.T = Theory(g, grow=1)
        cls.s = cls.T.solver()

    def d(self, prem, goal):
        return decide(self.T, prem, goal, self.s).kind

    def test_never_endomorphism(self):
        for m in (self.cay, self.pro):
            for prop in ("idempotent", "inner-aut"):
                self.assertEqual(self.d([], p(prop, m, False)), "выводится", (m, prop))
                self.assertEqual(self.d([p("trivial", self.G)], p(prop, m, False)), "выводится")

    def test_inclusion(self):
        for prop in ("idempotent", "inner-aut"):
            self.assertEqual(self.d([p(prop, self.inc)], p("abelian", self.G)), "выводится")
            self.assertEqual(self.d([p("abelian", self.G)], p(prop, self.inc)), "выводится")
            self.assertEqual(self.d([p("abelian", self.G, False)], p(prop, self.inc, False)), "выводится")

    def test_general_map(self):
        self.assertEqual(self.d([p("idempotent", self.F), p("abelian", self.G)], p("abelian", self.H)), "выводится")
        # без идемпотентности — нет
        self.assertEqual(self.d([p("abelian", self.G)], p("abelian", self.H)), "неизвестно")


class CayleySym(unittest.TestCase):
    """Характеризации 6.11.2026: Кэли — изоморфизм ⇔ |G| ⩽ 2; свойства Sym(G)."""

    @classmethod
    def setUpClass(cls):
        g = Graph(Vocab.section("grp"))
        cls.G = g.var("G", "Grp.obj")
        cls.A = g.given(g.make("aut", [cls.G]))
        cls.cA = g.given(g.make("cayley", [cls.A]))
        cls.S = g.given(g.make("sym", [cls.G]))
        cls.T = Theory(g, grow=1)
        cls.s = cls.T.solver()

    def d(self, prem, goal):
        return decide(self.T, prem, goal, self.s).kind

    def test_cayley_of_aut(self):
        # Aut(G) = 1 ⇔ |G| ⩽ 2, а Кэли Aut(G) нулевой ⇔ Aut(G) = 1
        self.assertEqual(self.d([p("cyclic", self.G, False)], p("zero-mor", self.cA, False)), "выводится")
        self.assertEqual(self.d([p("iso", self.cA)], p("abelian", self.A)), "выводится")

    def test_sym(self):
        self.assertEqual(self.d([p("finite", self.G, False)], p("perfect", self.S)), "выводится")
        self.assertEqual(self.d([p("finite", self.G, False)], p("amenable", self.S, False)), "выводится")
        self.assertEqual(self.d([p("finite", self.G), p("trivial", self.G, False)], p("perfect", self.S, False)), "выводится")
        self.assertEqual(self.d([p("centerless", self.S, False)], p("prime-order", self.G)), "выводится")  # |G| = 2
