"""2а (9.11): пакет правил A — Aut, Inn, Out, X/Z, X/Φ, X/X′ — согласен со строками библиотеки,
выводит задуманное и не выводит похожих ложных утверждений."""
import unittest

from algen.etalon import scheme
from algen.library import Library, Search
from algen.logic import Theory, Vocab, decide


def _theory(v, cond, goal):
    g, prem, gl = scheme(v, {"раздел": "grp", "условие": cond, "цель": goal})
    return g, prem, gl, Theory(g, grow=1, extra=[a for a, _ in prem + [gl] if a[0] == "r"])


class RulesATest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.lib = Library()
        cls.v = Vocab.section("grp")

    def _rows(self, goal):
        g, prem, gl, T = _theory(self.v, "∀ G : Grp", goal)
        S = Search(g, T, self.lib)
        s = T.solver()
        rows = bad = known = 0
        try:
            for env in S._assign(0, {}):
                facts, _ = S.facts(env)
                known += facts.get(gl[0]) is not None
                lits = []
                for a, val in facts.items():
                    l = T.lit(a, val)
                    if l is False:
                        bad += 1
                        break
                    if l is not None and l is not True:
                        lits.append(l)
                else:
                    if not s.solve(assumptions=lits):
                        bad += 1
                rows += 1
        finally:
            s.delete()
        return rows, bad, known

    def test_library_rows_agree(self):
        # цели, на атомах которых стоят правила пакета; строки — все группы библиотеки
        # (замер 9.11: строк 2769–3024, известных значений цели 495–1785, противоречий 0)
        for goal, min_known in (("iso(G, inn(G))", 1000), ("embeds(G, aut(G))", 400),
                                ("trivial(inn(G))", 1000), ("iso(G, aut(G))", 1000),
                                ("centerless(inn(G))", 1000), ("finite(commutator(G))", 1000),
                                ("embeds(aut(G), G)", 1000), ("prime-order(aut(G))", 1000),
                                ("locally-nilpotent(aut(G))", 600), ("odd-order(aut(G))", 1000),
                                ("trivial(frattini(quotient(G, frattini(G))))", 1000),
                                ("prime-orders(quotient(G, frattini(G)))", 1000),
                                ("cyclic(quotient(G, frattini(G)))", 1000),
                                ("centerless(quotient(G, center(G)))", 1000),
                                ("whole(inn(G))", 1000), ("nilpotent(inn(G))", 1000),
                                ("two-generated(inn(G))", 1000)):
            rows, bad, known = self._rows(goal)
            self.assertGreater(rows, 1000, goal)
            self.assertEqual(bad, 0, goal)
            self.assertGreater(known, min_known, goal)

    def test_derive(self):
        for cond, goal in (("centerless(G)", "iso(G, inn(G))"),
                           ("centerless(G)", "embeds(G, aut(G))"),
                           ("abelian(G)", "trivial(inn(G))"),
                           ("trivial(inn(G))", "abelian(G)"),
                           ("abelian(G)", "iso(aut(G), quotient(aut(G), inn(G)))"),
                           ("centerless(G), trivial(quotient(aut(G), inn(G)))", "iso(G, aut(G))"),
                           ("cyclic(inn(G))", "trivial(inn(G))"),
                           ("locally-cyclic(quotient(G, center(G)))", "abelian(G)"),
                           ("", "¬prime-order(inn(G))"),
                           ("finite(aut(G))", "finite(commutator(G))"),
                           ("simple(G), ¬abelian(G)", "simple(inn(G))"),
                           ("perfect(G)", "centerless(inn(G))"),
                           ("perfect(G)", "centerless(quotient(G, center(G)))"),
                           ("finite(G), iso(aut(G), inn(G))", "whole(inn(G))"),
                           ("finite(G), p-group(G), trivial(quotient(aut(G), inn(G)))", "cyclic(G)"),
                           ("prime-order(G)", "¬iso(G, aut(G))"),
                           ("¬left-orderable(G), embeds(G, aut(G))", "¬primitive(regular-act(G))"),
                           ("¬exponent-2(G), embeds(aut(G), G)", "¬primitive(regular-act(G))"),
                           ("cyclic(G), torsion-free(G), ¬simple(aut(G))", "primitive(regular-act(G))"),
                           ("exponent-2(G), abelian(aut(G))", "primitive(regular-act(G))"),
                           ("abelian(G), ¬exponent-2(G)", "¬odd-order(aut(G))"),
                           ("", "trivial(frattini(quotient(G, frattini(G))))"),
                           ("finite(G), iso(G, quotient(G, frattini(G)))", "trivial(frattini(G))"),
                           ("fin-gen(G), cyclic(quotient(G, frattini(G)))", "cyclic(G)"),
                           ("finite(G), p-group(G)", "prime-orders(quotient(G, frattini(G)))"),
                           ("nilpotent(G)", "nilpotent(inn(G))"),
                           ("periodic(G)", "periodic(inn(G))"),
                           ("exponent-3(G), ¬exponent-2(aut(G))", "¬primitive(regular-act(G))"),
                           ("cyclic(G), exponent-4(G), ¬prime-order(aut(G))", "primitive(regular-act(G))")):
            c = "∀ G : Grp" + (" | " + cond if cond else "")
            g, prem, gl, T = _theory(self.v, c, goal)
            self.assertEqual(decide(T, prem, gl).kind, "выводится", (cond, goal))

    def test_false_not_derived(self):
        # контрпримеры: Q₈ (Aut ≅ S₄ без подгруппы Q₈); ℤ(p^∞) (X/Φ = 1, X не циклична); C₄ (Φ = C₂);
        # C₃ (Out ≅ C₂); C₂ (Aut = 1 — p-группа); C₆ (X/Φ ≅ C₆); A₄ (без центра, Out ≅ C₂)
        for cond, goal in (("¬abelian(G)", "embeds(G, aut(G))"),
                           ("cyclic(quotient(G, frattini(G)))", "cyclic(G)"),
                           ("abelian(G)", "iso(G, quotient(G, frattini(G)))"),
                           ("nilpotent(G), finite(G)", "trivial(quotient(aut(G), inn(G)))"),
                           ("exponent-2(G)", "¬p-group(aut(G))"),
                           ("finite(G), nilpotent(G)", "prime-orders(quotient(G, frattini(G)))"),
                           ("centerless(G)", "whole(inn(G))")):
            c = "∀ G : Grp" + (" | " + cond if cond else "")
            g, prem, gl, T = _theory(self.v, c, goal)
            self.assertNotEqual(decide(T, prem, gl).kind, "выводится", (cond, goal))


if __name__ == "__main__":
    unittest.main()
