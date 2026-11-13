"""Φ(A × B) = Φ(A) × Φ(B) у построенных произведений: только при конечно
порождённых или абелевых множителях (library.synthesize_products)."""
import os
import unittest

os.environ.setdefault("ALGEN_SIZE", "2")

from algen.library import built_library
from algen.logic import Vocab


class ProductFrattini(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.lib = built_library(Vocab.section("grp"))

    def sub(self, key, field):
        o = self.lib.obj[key]
        return next(x for x in o["подгруппы"] if x["id"] == o[field])

    def test_finitely_generated_factors(self):
        # C₂ × SL(2, 5): Φ = 1 × {±E} ≅ C₂, фактор C₂ × A₅
        key = self.lib.prod["2:1", "120:5"]
        s = self.sub(key, "фраттини")
        self.assertEqual(s["≅"], "2:1")
        self.assertEqual(s["фактор"], self.lib.prod["2:1", "60:5"])
        self.assertTrue(s["свойства"]["normal"] and s["свойства"]["characteristic"])
        self.assertFalse(s["свойства"]["whole"])

    def test_not_written_without_proof(self):
        # бесконечно порождённый неабелев множитель: формула не доказана — Φ не пишется
        P = lambda k: self.lib.obj[k]["свойства"]
        fg = lambda k: P(k).get("fin-gen") or P(k).get("finite")
        n = 0
        for (a, b), key in self.lib.prod.items():
            o = self.lib.obj[key]
            if not o.get("синтез") or (fg(a) and fg(b)) or (P(a).get("abelian") and P(b).get("abelian")):
                continue
            n += 1
            self.assertIsNone(o.get("фраттини"), (a, b))
        self.assertGreater(n, 0)

    def test_abelian_factors(self):
        # абелевы множители, хотя бы один не к. п.: Φ = Φ(A) × Φ(B) (Φ(X) = ⋂ pX)
        P = lambda k: self.lib.obj[k]["свойства"]
        fg = lambda k: P(k).get("fin-gen") or P(k).get("finite")
        seen = 0
        for (a, b), key in self.lib.prod.items():
            o = self.lib.obj[key]
            if not (o.get("синтез") and P(a).get("abelian") and P(b).get("abelian")) or (fg(a) and fg(b)):
                continue
            fa, fb = (self.lib.obj[k].get("фраттини") for k in (a, b))
            if fa is None or fb is None:
                continue
            seen += 1
            self.assertIsNotNone(o.get("фраттини"), (a, b))
        self.assertGreater(seen, 0)


if __name__ == "__main__":
    unittest.main()
