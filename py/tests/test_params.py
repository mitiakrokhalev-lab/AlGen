"""Условия с параметрами: перебор примеров в таблице конечных групп.

    cd py && python3 -m unittest discover tests
"""

import unittest

from algen.params import Model, check, parse_formula


class ParamsTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.model = Model()

    def test_parse(self):
        f = parse_formula("cyclic(C(m) × C(n)) ⇔ gcd(m, n) = 1")
        self.assertEqual(f[0], "iff")
        self.assertEqual(parse_formula("ord(G) = 2p")[3], ("op", "·", ("int", 2), ("var", "p")))

    def test_true_on_examples(self):
        kind, _, n = check("∀ p : Prime; ∀ G : Grp | ord(G) = p^2", "abelian(G)", self.model)
        self.assertEqual(kind, "проверено")
        self.assertGreater(n, 0)

    def test_counterexample(self):
        kind, detail, _ = check("∀ p : Prime; ∀ G : Grp | ord(G) = p^3", "abelian(G)", self.model)
        self.assertEqual(kind, "опровергается")
        self.assertIn("p = 2", detail)

    def test_families(self):
        kind, _, _ = check("∀ k : ℕ | k ≥ 2, k ≤ 25", "ord(Z(D(2k))) = 2", self.model)
        self.assertEqual(kind, "проверено")
        kind, _, _ = check("∀ n : ℕ | n ≤ 50", "centerless(D(n))", self.model)
        self.assertEqual(kind, "опровергается")


if __name__ == "__main__":
    unittest.main()
