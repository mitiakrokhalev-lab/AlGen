"""Импорт π-Base: известные значения на месте, вывод не противоречив."""

import unittest

from algen.pibase import load, value

DB = load()


class PiBase(unittest.TestCase):
    def test_known_values(self):
        self.assertIs(value(DB, "S000043", "P000053"), False)  # прямая Зоргенфрея не метризуема
        self.assertIs(value(DB, "S000043", "P000013"), True)   # но нормальна
        self.assertIs(value(DB, "S000076", "P000013"), False)  # её квадрат не нормален
        self.assertIs(value(DB, "S000078", "P000007"), True)   # доска Тихонова компактна, T₄
        self.assertIs(value(DB, "S000079", "P000007"), False)  # проколотая — не T₄

    def test_every_derived_value_has_a_theorem(self):
        for s in DB["spaces"].values():
            for p, t in s["traits"].items():
                self.assertIn(t["by"], DB["theorems"])
                self.assertNotIn(p, s["asserted"])


if __name__ == "__main__":
    unittest.main()
