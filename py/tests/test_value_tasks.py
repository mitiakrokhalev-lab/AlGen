"""tools.value_tasks: виды неизвестных условий (A — ждёт одного значения, B — нескольких,
C — данных хватает) и подсчёт различных значений на маленькой таблице."""
import unittest

import numpy as np

from algen.enumerate import Form
from tools.value_tasks import classify, value_tasks


def fake(rows):
    """Атомы a, b, c — свойства G; строки — группы (верно / ложно / None)."""
    f = object.__new__(Form)
    m = np.zeros((len(rows), 6), dtype=bool)
    for r, row in enumerate(rows):
        for i, v in enumerate(row):
            if v is not None:
                m[r, 2 * i + (0 if v else 1)] = True
    f.m, f.fixed = m, []
    f.atoms = [("p", x, "G") for x in "abc"]
    f.value_name = lambda r, atom: f"{atom[1]}@{r}"
    return f


class ValueTasksTest(unittest.TestCase):
    def test_kinds(self):
        # условие a ⇒ c (запрет: a, ¬c): столбцы 0 (a верно) и 5 (c ложно)
        cols = [0, 5]
        # A: в строке 1 a верно, c неизвестно — значение c@1 решает
        f = fake([(True, None, True), (True, None, None), (False, None, False)])
        kind, pairs, n_multi, n_allt = classify(f, cols)
        self.assertEqual((kind, pairs, n_multi, n_allt), ("A", [(1, 5)], 0, 0))
        # B: в строке 0 неизвестны и a, и c
        f = fake([(None, None, None), (True, None, True)])
        self.assertEqual(classify(f, cols)[0], "B")
        # C: данных хватает — в каждой строке какой-то литерал запрета ложен
        f = fake([(True, None, True), (False, True, False)])
        self.assertEqual(classify(f, cols)[0], "C")
        # опровергающая строка видна (её быть не должно у живого условия)
        f = fake([(True, None, False)])
        self.assertEqual(classify(f, cols)[3], 1)

    def test_summary(self):
        f = fake([(True, None, None), (True, None, None), (None, True, False), (False, False, False)])
        report = [
            # a ⇒ c (запрет a, ¬c): строки 0, 1 — неизвестно c; строка 2 — неизвестно a
            {"вердикт": "неизвестно", "_cols": [0, 5], "примеров": 2},
            # b ⇒ a (запрет b, ¬a): строка 2 — неизвестно a
            {"вердикт": "неизвестно", "_cols": [2, 1], "примеров": 1, "свёрнута": True},
            # c ⇒ a (запрет c, ¬a): в каждой строке литерал ложен — вид C
            {"вердикт": "неизвестно", "_cols": [4, 1], "примеров": 0},
            {"вердикт": "выводится", "_cols": [0, 4]},
        ]
        vt = value_tasks(f, report)
        allu = vt["все неизвестные"]
        self.assertEqual(allu["условий"], 3)
        self.assertEqual(allu["по видам"], {"A": 2, "C": 1})
        self.assertEqual(allu["_значения"], {"c@0": 1, "c@1": 1, "a@2": 2})
        self.assertEqual(allu["различных значений (A)"], 3)
        self.assertEqual(allu["опровергающих строк (должно быть 0)"], 0)
        self.assertEqual(allu["опора условий C"], {"0": 1})
        # самое частое значение a@2 затрагивает оба условия A
        self.assertEqual(allu["покрытие условий A первыми значениями"]["100 %"], 1)
        kept = vt["оставленные после сжатия"]
        self.assertEqual(kept["условий"], 2)
        self.assertEqual(kept["по видам"], {"A": 1, "C": 1})
        self.assertEqual(kept["различных значений (A)"], 3)

if __name__ == "__main__":
    unittest.main()
