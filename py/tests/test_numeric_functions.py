"""Я1 (8.11): числовые функции группы exp(G) и k(G) — значения библиотеки и правила.

Значения конечных групп посчитаны GAP (экспонента — props2, классы — grp-elts) и
сверены между собой; здесь каждая строка библиотеки подставляется в теорию с
новыми правилами: противоречие значит ошибку правила или данных.
"""
import unittest
from math import gcd

from algen.etalon import scheme
from algen.library import INF, Library, Search
from algen.logic import Theory, Vocab, decide


class NumericFunctionsTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.lib = Library()
        cls.v = Vocab.section("grp")

    def test_values_agree_with_classes(self):
        checked = 0
        for k, o in self.lib.obj.items():
            if not o.get("конечная") or not o.get("элементы"):
                continue
            els = o["элементы"]
            lcm = 1
            for c in els:
                lcm = lcm * c["ord"] // gcd(lcm, c["ord"])
            order = int(k.split(":")[0])
            self.assertEqual(sum(c["size"] for c in els), order, k)
            S = Search.__new__(Search)
            S.lib = self.lib
            self.assertEqual(S._im_exponent(("obj", k)), lcm, k)
            self.assertEqual(S._im_classes(("obj", k)), len(els), k)
            # численные следствия правил
            self.assertEqual(order % lcm, 0, k)
            self.assertLessEqual(len(els), order, k)
            self.assertEqual(len(els) == order, o["свойства"].get("abelian") is True, k)
            if len(els) == 2:
                self.assertEqual(order, 2, k)
            if order % 2 == 0:
                self.assertEqual(lcm % 2, 0, k)
            checked += 1
        self.assertGreater(checked, 1000)

    def test_infinite_values(self):
        S = Search.__new__(Search)
        S.lib = self.lib
        for k, o in self.lib.obj.items():
            if o.get("конечная"):
                continue
            pr = o.get("свойства", {})
            e, c = S._im_exponent(("obj", k)), S._im_classes(("obj", k))
            if pr.get("bounded-exponent") is False:
                self.assertEqual(e, INF, k)
            if pr.get("abelian") is True and pr.get("finite") is False:
                self.assertEqual(c, INF, k)
            if e is not None and e != INF:
                self.assertIs(pr.get("bounded-exponent"), True, k)

    def _rows_consistent(self, goal_terms):
        g, prem, goal = scheme(self.v, {"раздел": "grp", "условие": "∀ G : Grp", "цель": goal_terms})
        T = Theory(g, grow=1, extra=[a for a, _ in [goal] if a[0] == "r"])
        S = Search(g, T, self.lib)
        s = T.solver()
        rows = bad = 0
        try:
            for env in S._assign(0, {}):
                facts, _ = S.facts(env)
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
        return rows, bad

    def test_library_rows_agree_with_rules(self):
        for goal in ("num-eq(num-classes(G), ord(G))", "num-divides(exponent(G), ord(G))",
                     "num-le(num-classes(G), ord(G))", "num-two(num-classes(G))", "num-one(num-classes(G))",
                     "num-even(exponent(G))", "num-two(exponent(G))", "num-one(exponent(G))",
                     "num-finite(exponent(G))", "num-finite(num-classes(G))"):
            rows, bad = self._rows_consistent(goal)
            self.assertGreater(rows, 1000, goal)
            self.assertEqual(bad, 0, goal)

    def test_false_statement_is_refuted_by_rows(self):
        # контроль: ложное «конечная ⇒ exp(G) = |G|» не выводится, а строки V₄ и др. его опровергают
        g, prem, gl = scheme(self.v, {"раздел": "grp", "условие": "∀ G : Grp | finite(G)",
                                      "цель": "num-eq(exponent(G), ord(G))"})
        T = Theory(g, grow=1, extra=[gl[0]])
        self.assertNotEqual(decide(T, prem, gl).kind, "выводится")
        S = Search(g, T, self.lib)
        refuting = 0
        for env in S._assign(0, {}):
            facts, _ = S.facts(env)
            if all(facts.get(a) == val for a, val in prem) and facts.get(gl[0]) is False:
                refuting += 1
        self.assertGreater(refuting, 100)

    def test_rules_derive(self):
        cases = [("∀ G : Grp | finite(G), abelian(G)", "num-eq(num-classes(G), ord(G))", "выводится"),
                 ("∀ G : Grp | finite(G), num-eq(num-classes(G), ord(G))", "abelian(G)", "выводится"),
                 ("∀ G : Grp | finite(G)", "num-divides(exponent(G), ord(G))", "выводится"),
                 ("∀ G : Grp | bounded-exponent(G)", "num-finite(exponent(G))", "выводится"),
                 ("∀ G : Grp | finite(G), num-two(num-classes(G))", "num-two(ord(G))", "выводится")]
        for cond, goal, want in cases:
            g, prem, gl = scheme(self.v, {"раздел": "grp", "условие": cond, "цель": goal})
            T = Theory(g, grow=1, extra=[a for a, _ in prem + [gl] if a[0] == "r"])
            self.assertEqual(decide(T, prem, gl).kind, want, (cond, goal))


if __name__ == "__main__":
    unittest.main()
