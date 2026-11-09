"""Подпись недостающего значения: для G/N называется то, чего нет, — сама N или фактор."""
import unittest
from types import SimpleNamespace

from algen.enumerate import Form
from algen.logic import App, Var

G = Var("G")
PHI, Z = App("frattini", (G,)), App("center", (G,))


class Stub:
    _value_name = Form._value_name

    def __init__(self, images, lib):
        self.images, self.lib = images, lib

    def _image(self, r, t):
        return self.images.get(t)

    def where(self, r):
        return "строка"


def lib():
    return SimpleNamespace(obj={"SU2": {"имя": "SU(2)", "свойства": {}}})


class ValueName(unittest.TestCase):
    def test_missing_frattini(self):
        s = Stub({G: ("obj", "SU2")}, lib())
        self.assertEqual(s._value_name(0, ("p", "abelian", App("quotient", (G, PHI)))), "не записан фраттини у SU(2)")
        self.assertEqual(s._value_name(0, ("p", "abelian", PHI)), "не записан фраттини у SU(2)")

    def test_missing_factor(self):
        s = Stub({G: ("obj", "SU2"), Z: ("sub", "SU2", 1)}, lib())
        self.assertEqual(s._value_name(0, ("p", "abelian", App("quotient", (G, Z)))),
                         f"не записан фактор по {Z} у SU(2)")

    def test_missing_center(self):
        s = Stub({G: ("obj", "SU2")}, lib())
        self.assertEqual(s._value_name(0, ("p", "abelian", App("quotient", (G, Z)))), "не записан центр у SU(2)")


if __name__ == "__main__":
    unittest.main()
