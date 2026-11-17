"""Я2: «тождество ⇒ тождество» с сертификатами (Тодд–Коксетер, Кнут–Бендикс)."""
import unittest

from algen.identities import parse
from algen.laws import TooBig, act, decide_laws, law_holds_in, todd_coxeter


def order(gens, rels):
    return len(todd_coxeter(gens, [parse(r) for r in rels])[(gens[0], 1)])


class LawsTest(unittest.TestCase):
    def test_coset_enumeration_known_groups(self):
        for gens, rels, n in ((["x", "y"], ["x^2", "y^2", "(xy)^2"], 4), (["x", "y"], ["x^2", "y^3", "(xy)^2"], 6),
                              (["x", "y"], ["x^2", "y^2", "(xy)^5"], 10), (["x", "y"], ["x^4", "x^2y^-2", "y^-1xyx"], 8),
                              (["x", "y"], ["x^2", "y^3", "(xy)^5"], 60), (["x", "y"], ["x^2", "y^3", "(xy)^4"], 24),
                              (["x", "y"], ["x^2", "y^3", "(xy)^7", "[x,y]^4"], 168), (["x"], ["x^5"], 5)):
            self.assertEqual(order(gens, rels), n, rels)

    def test_too_big(self):
        with self.assertRaises(TooBig):
            todd_coxeter(["x", "y"], [parse("x^2"), parse("y^3")], limit=500)  # C₂ ∗ C₃ бесконечна

    def test_law_check_in_finite_group(self):
        q8 = todd_coxeter(["x", "y"], [parse(r) for r in ["x^4", "x^2y^-2", "y^-1xyx"]])
        self.assertTrue(law_holds_in(q8, ["x", "y"], 8, parse("x^4")))
        self.assertFalse(law_holds_in(q8, ["x", "y"], 8, parse("x^2")))
        self.assertTrue(law_holds_in(q8, ["x", "y"], 8, parse("[x, y, z]")))
        self.assertNotEqual(act(q8, parse("[x, y]")), 0)

    def test_textbook_pairs(self):
        cases = [("x^2 = 1", "[x, y] = 1", "выводится"),
                 ("x^3 = 1", "[x, y] = 1", "опровергается"),
                 ("(ab)^2 = a^2 b^2", "[x, y] = 1", "выводится"),
                 ("(ab)^-1 = a^-1 b^-1", "[x, y] = 1", "выводится"),
                 ("(ab)^3 = a^3 b^3", "[x, y] = 1", "опровергается"),
                 ("x^4 = 1", "[x, y] = 1", "опровергается"),
                 ("[x, y] = 1", "x^2 = 1", "опровергается")]
        for p, g, want in cases:
            self.assertEqual(decide_laws(p, g)[0], want, (p, g))


if __name__ == "__main__":
    unittest.main()


class LawsReviewTest(unittest.TestCase):
    """Замечания ревью 8.11: пропущенное совпадение в scan, проверка таблиц, дешёвые выводы."""

    def test_trivial_group_found(self):
        from algen.laws import valid_table
        rels = [parse("y^3"), parse("y x^-1 y x^-3"), parse("x^-1 y^3")]
        t = todd_coxeter(["x", "y"], rels)
        self.assertEqual(len(t[("x", 1)]), 1)  # x = y³ = 1, y² = 1 ⇒ группа тривиальна
        self.assertTrue(valid_table(t, ["x", "y"], rels))

    def test_order_independent_of_relator_order(self):
        rels = ["x y^-1", "x^-1 y^2 x^2", "x^-1 y^-1 x^-1 y", "x^-2 y^-2"]
        orders = {len(todd_coxeter(["x", "y"], [parse(r) for r in perm])[("x", 1)])
                  for perm in (rels, rels[::-1], rels[1:] + rels[:1])}
        self.assertEqual(orders, {1})

    def test_random_presentations_give_valid_tables(self):
        import random
        from algen.laws import valid_table
        rng = random.Random(5)
        letters = ["x", "x^-1", "y", "y^-1"]
        checked = 0
        for _ in range(300):
            rels = [parse(" ".join(rng.choice(letters) for _ in range(rng.randint(2, 6)))) for _ in range(3)]
            rels = [r for r in rels if r]
            try:
                t = todd_coxeter(["x", "y"], rels, limit=3000)
            except TooBig:
                continue
            self.assertTrue(valid_table(t, ["x", "y"], rels), rels)
            n = len(t[("x", 1)])
            rng.shuffle(rels)
            self.assertEqual(len(todd_coxeter(["x", "y"], [list(reversed(r)) and r for r in rels], limit=3000)[("x", 1)]), n)
            checked += 1
        self.assertGreater(checked, 100)

    def test_cheap_derivations(self):
        self.assertEqual(decide_laws("[x, y] = [y, x]", "[x, y]^2 = 1")[0], "выводится")
        self.assertEqual(decide_laws("[x, y, z] = 1", "[x y, z] = [x, z][y, z]")[0], "выводится")
        self.assertEqual(decide_laws("[x, y, z] = 1", "[x, y] = 1")[0], "опровергается")
