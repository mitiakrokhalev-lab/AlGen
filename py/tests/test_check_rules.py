"""Проверщик правил ловит заведомо ложное правило и не трогает верное.

    cd py && python3 -m unittest discover tests
"""

import unittest

from algen.check_rules import Table, check
from algen.finite import load, load_products

TABLE = Table(load(), load_products())
X = {"name": "X", "sort": "Grp.obj"}
N = {"name": "N", "sort": "Grp.sub", "ambient": "X"}


def rule(scene, prem, concl):
    return {"id": "тест", "scene": scene, "if": prem, "then": concl}


class CheckRules(unittest.TestCase):
    def test_false_rule_is_caught(self):
        r = rule([X], [{"p": "abelian", "t": "X"}], {"p": "cyclic", "t": "X"})
        res, first = check(r, TABLE, 32)
        self.assertGreater(res["НАРУШЕНО"], 0)
        self.assertEqual(first[0], "НАРУШЕНО")

    def test_true_rule_holds(self):
        # G/Z(G) циклична ⇒ G абелева
        q = {"op": "quotient", "args": ["X", {"op": "center", "args": ["X"]}]}
        r = rule([X], [{"p": "cyclic", "t": q}], {"p": "abelian", "t": "X"})
        res, _ = check(r, TABLE, 32)
        self.assertEqual(res["НАРУШЕНО"], 0)
        self.assertGreater(res["верно"], 100)

    def test_quotient_by_non_normal_does_not_count(self):
        q = {"op": "quotient", "args": ["X", "N"]}
        r = rule([X, N], [], {"p": "finite", "t": q})
        res, _ = check(r, TABLE, 32)
        self.assertEqual(res["НАРУШЕНО"], 0)
        self.assertGreater(res["вывод не определён"], 0)

    def test_maximal_normal_has_prime_index(self):
        # Нормальная максимальная подгруппа имеет простой индекс (эталон E-grp-05).
        idx = {"op": "index", "args": ["X", "N"]}
        r = rule([X, N], [{"p": "normal", "t": "N"}, {"p": "maximal", "t": "N"}],
                 {"p": "num-prime", "t": idx})
        res, _ = check(r, TABLE, 32)
        self.assertEqual(res["НАРУШЕНО"], 0)
        self.assertGreater(res["верно"], 1000)


if __name__ == "__main__":
    unittest.main()
