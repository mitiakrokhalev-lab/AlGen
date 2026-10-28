"""Перебор условий: отсев по матрице библиотеки и минимальность.

    cd py && python3 -m unittest discover tests
"""

import unittest

import numpy as np

from algen.enumerate import enumerate_form, minimal


class FakeForm:
    """Три атома a, b, c; строки — объекты библиотеки (верно / ложно / None)."""

    def __init__(self, rows):
        self.on_q, self.normal = set(), 0
        m = np.zeros((len(rows), 6), dtype=bool)
        for r, row in enumerate(rows):
            for i, v in enumerate(row):
                if v is not None:
                    m[r, 2 * i + (0 if v else 1)] = True
        self.e = self.m = m


class EnumerateTest(unittest.TestCase):
    def test_refuted_and_minimal(self):
        # a ⇒ c на всех строках, b ⇒ c опровергается последней строкой.
        form = FakeForm([(True, True, True), (True, False, True), (False, True, False)])
        alive, empty = enumerate_form(form, 2, goals=[4])
        self.assertIn(((0,), 4), alive)
        self.assertNotIn(((2,), 4), alive)
        # a, b ⇒ c не минимально: хватает a.
        self.assertIn(((0, 2), 4), alive)
        mins = minimal(alive)
        self.assertIn(((0,), 4), mins)
        self.assertNotIn(((0, 2), 4), mins)

    def test_unknown_value_does_not_refute(self):
        # Значение цели не записано: строка не опровергает.
        form = FakeForm([(True, None, None)])
        alive, _ = enumerate_form(form, 1, goals=[4, 5])
        self.assertIn(((0,), 4), alive)
        self.assertIn(((0,), 5), alive)


if __name__ == "__main__":
    unittest.main()
