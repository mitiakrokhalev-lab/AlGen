"""Тождества в элементах: свободная и свободная нильпотентная группа.

    cd py && python3 -m unittest discover tests
"""

import unittest

from algen.identities import holds, parse


def check(s, c=None):
    lhs, rhs = s.split("=")
    return holds(parse(lhs), parse(rhs), c)[0]


class IdentitiesTest(unittest.TestCase):
    def test_all_groups(self):
        self.assertTrue(check("[a b, c] = [a, c]^b [b, c]"))
        self.assertTrue(check("[a, b⁻¹, c]^b [b, c⁻¹, a]^c [c, a⁻¹, b]^a = 1"))  # Холл–Витт
        self.assertFalse(check("[a b, c] = [a, c][b, c]"))

    def test_nilpotent(self):
        # Задачник Дыбковой, 5.13: в ступени 2 коммутатор билинеен, в ступени 3 уже нет.
        self.assertTrue(check("[a b, c] = [a, c][b, c]", 2))
        self.assertFalse(check("[a b, c] = [a, c][b, c]", 3))
        self.assertTrue(check("(a b)^2 = a^2 b^2 [b, a]", 2))
        self.assertTrue(check("a b = b a", 1))
        self.assertFalse(check("a b = b a", 2))


if __name__ == "__main__":
    unittest.main()
