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
        # множитель бесконечно порождённый и неабелев: формула не доказана — Φ не пишется
        P = lambda k: self.lib.obj[k]["свойства"]
        ok = lambda k: P(k).get("fin-gen") or P(k).get("finite") or P(k).get("abelian")
        n = 0
        for (a, b), key in self.lib.prod.items():
            o = self.lib.obj[key]
            if not o.get("синтез") or (ok(a) and ok(b)):
                continue
            n += 1
            self.assertIsNone(o.get("фраттини"), (a, b))
        self.assertGreater(n, 0)

    def test_mixed_fg_and_abelian(self):
        # к. п. × абелева (не к. п.): Φ(A × B) = Φ(A) × Φ(B) — центральный множитель
        P = lambda k: self.lib.obj[k]["свойства"]
        fg = lambda k: P(k).get("fin-gen") or P(k).get("finite")
        seen = 0
        for (a, b), key in self.lib.prod.items():
            o = self.lib.obj[key]
            if not o.get("синтез") or not (fg(a) and not P(a).get("abelian") and P(b).get("abelian") and not fg(b)):
                continue
            if self.lib.obj[a].get("фраттини") is None or self.lib.obj[b].get("фраттини") is None:
                continue
            seen += 1
            self.assertIsNotNone(o.get("фраттини"), (a, b))
        self.assertGreater(seen, 0)

    def test_prime_cyclic_factor_maximal(self):
        # A × 1 ⊂ A × C_p индекса p максимальна и при C_p из бесконечного файла (p > 10⁷⁵)
        key = self.lib.prod["Q", "Cp"]
        o = self.lib.obj[key]
        a1 = next(x for x in o["подгруппы"] if x.get("пара") and x["≅"] == "Q" and x.get("фактор") == "Cp")
        self.assertTrue(a1["свойства"]["maximal"])
        phi = next(x for x in o["подгруппы"] if x["id"] == o["фраттини"])
        self.assertTrue(phi["свойства"]["maximal"])  # Φ(ℚ × C_p) = ℚ × 1

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
