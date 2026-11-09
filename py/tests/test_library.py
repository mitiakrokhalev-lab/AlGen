"""Библиотека групп: записи совместны с базой, контрпримеры находятся.

    cd py && python3 -m unittest discover tests
"""

import unittest

from algen.library import Library, Scene, jobs
from algen.logic import Vocab


class LibraryTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.lib = Library()
        cls.sc = Scene(Vocab.section("grp"))

    def test_infinite_records_agree_with_rules(self):
        for key, sub in jobs(self.lib, self.lib.infinite()):
            self.assertIsNone(self.sc.check(self.sc.facts(self.lib, key, sub)), (key, sub))

    def test_finite_records_agree_with_rules(self):
        # Конечные значения посчитаны GAP: противоречие здесь — ложное правило
        # или ошибка движка.
        keys = [k for k, o in self.lib.obj.items() if o["конечная"]][::25]
        for key, sub in jobs(self.lib, keys):
            self.assertIsNone(self.sc.check(self.sc.facts(self.lib, key, sub)), (key, sub))

    def test_counterexample_is_found(self):
        # к. п. G, разрешимая нормальная N — не обязательно к. п.: BS(1, 2) и ℤ[1/2].
        sc = self.sc
        prem = [(("p", "fin-gen", sc.G), True), (("p", "normal", sc.N), True),
                (("p", "solvable", sc.N), True)]
        found = sc.witnesses(self.lib, prem, (("p", "fin-gen", sc.N), True))
        self.assertTrue(found)
        self.assertFalse(self.lib.obj[found[0]["G"]]["конечная"])

    def test_true_statement_has_no_counterexample(self):
        sc = self.sc
        prem = [(("p", "normal", sc.N), True), (("p", "maximal", sc.N), True)]
        self.assertEqual(sc.witnesses(self.lib, prem, (("p", "finite-index", sc.N), True)), [])



class SearchTest(unittest.TestCase):
    def test_two_groups(self):
        # A ф. а. ⇒ A × B ф. а.? Нет: B = ℚ. Значение для A × B выводится из правил.
        from algen.etalon import scheme
        from algen.library import Search
        from algen.logic import Theory
        v = Vocab.section("grp")
        fact = {"раздел": "grp", "условие": "∀ A : Grp | residually-finite(A); ∀ B : Grp",
                "цель": "residually-finite(A × B)"}
        g, prem, goal = scheme(v, fact)
        found = Search(g, Theory(g), Library()).witnesses(prem, goal, limit=1)
        self.assertTrue(found)


if __name__ == "__main__":
    unittest.main()


class SymKeyTest(unittest.TestCase):
    def test_sym_key_huge_and_nested(self):
        """Sym(Sym(X)) при большом |X|: card = n! — ключ без десятичной записи,
        порядок не пишется (пилот 15 падал: «Exceeds the limit (4300 digits)»)."""
        from math import factorial
        from algen.library import Library
        lib = Library.__new__(Library)
        lib.obj = {}
        for n in (7, 150, 151, 2000, factorial(2000)):
            k = lib.sym_key(n)
            self.assertIn(k, lib.obj)
            o = lib.obj[k]
            self.assertEqual(o["порядок"], factorial(n) if n <= 150 else None)
            self.assertTrue(o.get("неканонический"))
            str(o)  # всё печатается
        self.assertNotEqual(lib.sym_key(factorial(2000)), lib.sym_key(factorial(2000) + 1))


class RankTest(unittest.TestCase):
    """d(G): поле «ранг», 1 и циклические, не к. п.; A × B — max при взаимно простых
    порядках, сумма при тривиальном множителе, иначе неизвестно."""

    def test_key_rank(self):
        from types import SimpleNamespace
        from algen.library import INF, Search
        obj = {
            "1:1": {"конечная": True, "свойства": {"trivial": True}},
            "4:2": {"конечная": True, "свойства": {"trivial": False, "cyclic": False}, "ранг": 2},
            "3:1": {"конечная": True, "свойства": {"trivial": False, "cyclic": True}},
            "6:1": {"конечная": True, "свойства": {"trivial": False, "cyclic": False}, "ранг": 2},
            "Q": {"конечная": False, "свойства": {"finite": False, "fin-gen": False}},
            "P1": {"конечная": True, "свойства": {}}, "P2": {"конечная": True, "свойства": {}},
            "P3": {"конечная": True, "свойства": {}},
        }
        prod = {("4:2", "3:1"): "P1", ("4:2", "6:1"): "P2", ("1:1", "6:1"): "P3"}
        sc = Search.__new__(Search)
        sc.lib = SimpleNamespace(obj=obj, prod=prod)
        r = sc._key_rank
        self.assertEqual([r("1:1"), r("3:1"), r("4:2"), r("Q")], [0, 1, 2, INF])
        self.assertEqual(r("P1"), 2)      # V₄ × C₃: порядки 4 и 3 взаимно просты
        self.assertIsNone(r("P2"))        # V₄ × C₆: не взаимно просты — не знаем
        self.assertEqual(r("P3"), 2)      # 1 × C₆
