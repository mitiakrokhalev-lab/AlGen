"""2а.3: ключи построенных групп библиотеки → выражения GAP (props2x)."""
import unittest

from algen.finite import gap_expr


class GapExprTest(unittest.TestCase):
    def test_keys(self):
        self.assertEqual(gap_expr("16:14"), "SmallGroup(16, 14)")
        self.assertEqual(gap_expr("20160:Aut(16:14)"), "AutomorphismGroup(AsPc(SmallGroup(16, 14)))")
        self.assertEqual(gap_expr("768:Out(32:46)"), "OutGroup(AutomorphismGroup(AsPc(SmallGroup(32, 46))))")
        self.assertEqual(gap_expr("768:G′(6144:Aut(64:247))"),
                         "DerivedSubgroup(AsPc(AutomorphismGroup(AsPc(SmallGroup(64, 247)))))")
        self.assertEqual(gap_expr("73728:147456:Aut(64:192)/Z"),
                         "QZ(AsPc(AutomorphismGroup(AsPc(SmallGroup(64, 192)))))")
        self.assertEqual(gap_expr("512:2048:Aut(64:225)/Φ"),
                         "QF(AsPc(AutomorphismGroup(AsPc(SmallGroup(64, 225)))))")
        self.assertIsNone(gap_expr("Sym(7)"))
        self.assertIsNone(gap_expr("12:weird"))


if __name__ == "__main__":
    unittest.main()
