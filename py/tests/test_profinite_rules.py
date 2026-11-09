"""2а.2 (8.11): правила о проконечном пополнении X̂ согласны со строками библиотеки и выводят нужное."""
import unittest

from algen.etalon import scheme
from algen.library import Library, Search
from algen.logic import Theory, Vocab, decide


class ProfiniteRulesTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.lib = Library()
        cls.v = Vocab.section("grp")

    def _rows(self, goal):
        g, prem, gl = scheme(self.v, {"раздел": "grp", "условие": "∀ G : Grp", "цель": goal})
        T = Theory(g, grow=1, extra=[gl[0]] if gl[0][0] == "r" else [])
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
        for goal in ("iso(G, profinite(G))", "trivial(profinite(G))", "abelian(profinite(G))",
                     "finite(profinite(G))", "countable(profinite(G))", "nilpotent(profinite(G))",
                     "bounded-exponent(profinite(G))"):
            rows, bad, known = self._rows(goal)
            self.assertGreater(rows, 1000, goal)
            self.assertEqual(bad, 0, goal)

    def test_derive(self):
        for cond, goal in (("∀ G : Grp | finite(G)", "iso(G, profinite(G))"),
                           ("∀ G : Grp | trivial(G)", "trivial(profinite(G))"),
                           ("∀ G : Grp | trivial(G)", "iso(frattini(G), profinite(G))"),
                           ("∀ G : Grp | no-finite-quotients(G)", "trivial(profinite(G))"),
                           ("∀ G : Grp | abelian(G)", "abelian(profinite(G))"),
                           ("∀ G : Grp | ¬finite(profinite(G))", "¬countable(profinite(G))")):
            g, prem, gl = scheme(self.v, {"раздел": "grp", "условие": cond, "цель": goal})
            T = Theory(g, grow=1, extra=[a for a, _ in prem + [gl] if a[0] == "r"])
            self.assertEqual(decide(T, prem, gl).kind, "выводится", (cond, goal))

    def test_false_not_derived(self):
        # Ẑ: пополнение ℤ не к. п. и без кручения у ℤ не переносится обратно; X̂ ≇ X для ℤ
        for cond, goal in (("∀ G : Grp | fin-gen(G)", "fin-gen(profinite(G))"),
                           ("∀ G : Grp | residually-finite(G)", "iso(G, profinite(G))")):
            g, prem, gl = scheme(self.v, {"раздел": "grp", "условие": cond, "цель": goal})
            T = Theory(g, grow=1, extra=[a for a, _ in prem + [gl] if a[0] == "r"])
            self.assertNotEqual(decide(T, prem, gl).kind, "выводится", (cond, goal))


if __name__ == "__main__":
    unittest.main()
