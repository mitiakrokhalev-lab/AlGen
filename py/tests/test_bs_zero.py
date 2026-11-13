"""BS(m, n) при нулевом аргументе (ранг тривиальной группы — 0): BS(0, 0) = F₂, BS(0, 1) = ℤ,
BS(0, n) = C_n ∗ ℤ — с кручением и ф. а. Ложные прежде выводы «без кручения» и «не ф. а.»
теперь не выводятся; верные при ненулевых аргументах — выводятся (ревью 13.11)."""
import unittest

from algen.etalon import scheme
from algen.logic import Theory, Vocab, decide

AB = "∀ A : Grp; ∀ B : Grp | "


class BSZeroTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.v = Vocab.section("grp")

    def _kind(self, cond, goal):
        g, prem, gl = scheme(self.v, {"раздел": "grp", "условие": cond, "цель": goal})
        T = Theory(g, grow=1, extra=[a for a, _ in prem + [gl] if a[0] == "r"])
        return decide(T, prem, gl).kind

    def test_zero_not_derived(self):
        # rank(A) = 0, ord(B) = p: BS(0, p) = C_p ∗ ℤ — есть кручение, ф. а.
        for cond, goal in (
                (AB + "trivial(A), prime-order(B)", "torsion-free(bs(rank(A), ord(B)))"),
                (AB + "trivial(A), ¬num-one(rank(A)), prime-order(B), ¬num-eq(rank(A), ord(B))",
                 "¬residually-finite(bs(rank(A), ord(B)))")):
            self.assertNotEqual(self._kind(cond, goal), "выводится", (cond, goal))

    def test_nonzero_derived(self):
        for cond, goal in (
                ("∀ G : Grp | prime-order(G)", "torsion-free(bs(ord(G), ord(G)))"),
                ("∀ G : Grp", "torsion-free(bs(rank(G), rank(G)))"),
                (AB + "prime-order(A), prime-order(B), ¬num-eq(ord(A), ord(B))",
                 "¬residually-finite(bs(ord(A), ord(B)))"),
                (AB + "prime-order(A), prime-order(B)", "torsion-free(bs(ord(A), ord(B)))")):
            self.assertEqual(self._kind(cond, goal), "выводится", (cond, goal))


if __name__ == "__main__":
    unittest.main()
