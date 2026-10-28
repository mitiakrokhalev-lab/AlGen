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


if __name__ == "__main__":
    unittest.main()
