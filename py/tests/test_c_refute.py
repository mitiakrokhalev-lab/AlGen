"""tools.c_refute: перевод вопросов C в предикаты GAP (без запуска GAP)."""
import unittest

from tools.c_refute import Unsupported, script, translate


class CRefuteTest(unittest.TestCase):
    def test_translate_shares_subterms_and_negates(self):
        body, dear = translate("centerless(frattini(G)) & odd-order(G) & ¬centerless(quotient(G, frattini(G)))")
        self.assertFalse(dear)
        self.assertEqual(body.count("FrattiniSubgroup(G)"), 1)  # подтерм считается один раз
        self.assertIn("QuotientBy(G, t1)", body)
        self.assertIn("if not not (Size(Centre(t2)) = 1) then return false; fi;", body)
        self.assertTrue(body.rstrip().endswith("return true;"))

    def test_relations_aut_and_regular_action(self):
        body, dear = translate("embeds(aut(commutator(G)), G) & prime-order(aut(G)) & ¬primitive(regular-act(G))")
        self.assertTrue(dear)  # Aut — только малые порядки
        self.assertIn("EmbedsG(", body)
        self.assertIn("IsPrimeInt(Size(G))", body)

    def test_unsupported_is_reported(self):
        with self.assertRaises(Exception):
            translate("whitehead(G) & indecomposable(G)")
        text, preds, skipped = script(["whitehead(G) & abelian(G)", "abelian(G) & ¬cyclic(G)"], "/tmp/x.jsonl",
                                      100, 100, 10, 1)
        self.assertEqual(len(preds), 1)
        self.assertEqual(len(skipped), 1)
        self.assertIn("P1 := function(G)", text)
        self.assertIn("CALL_WITH_CATCH", text)


if __name__ == "__main__":
    unittest.main()
