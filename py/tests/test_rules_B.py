"""Пакет B (9.11): правила о pullback, pushout, equalizer, coequalizer, Sym(X) и вложении Кэли
согласны со строками библиотеки, выводят нужное и не выводят похожее ложное."""
import sys
import unittest

from algen.etalon import scheme
from algen.library import Library, Search
from algen.logic import Theory, Vocab, decide

C, S = "cayley(G)", "sym(G)"
PB, PO = f"pullback({C}, {C})", f"pushout({C}, {C})"
GHF = "∀ G : Grp; ∀ H : Grp; ∀ F : Mor(G, H)"
GHF2 = "∀ G : Grp; ∀ H : Grp; ∀ F : Mor(G, H); ∀ E : Mor(G, H)"


class RulesBTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.lib = Library()
        cls.v = Vocab.section("grp")

    def _rows(self, goal):
        g, prem, gl = scheme(self.v, {"раздел": "grp", "условие": "∀ G : Grp", "цель": goal})
        T = Theory(g, grow=1, extra=[gl[0]] if gl[0][0] == "r" else [])
        S_ = Search(g, T, self.lib)
        s = T.solver()
        rows = bad = known = 0
        try:
            for env in S_._assign(0, {}):
                facts, _ = S_.facts(env)
                known += facts.get(gl[0]) is not None
                lits = []
                for a, val in facts.items():
                    l = T.lit(a, val)
                    if l is False:
                        bad += 1
                        break
                    if l is not None and l is not True:
                        lits.append(l)
                else:
                    if not s.solve(assumptions=lits):
                        bad += 1
                rows += 1
        finally:
            s.delete()
        return rows, bad, known

    def _kind(self, quant, cond, goal):
        g, prem, gl = scheme(self.v, {"раздел": "grp", "условие": quant + (" | " + cond if cond else ""),
                                      "цель": goal})
        T = Theory(g, grow=1, extra=[a for a, _ in prem + [gl] if a[0] == "r"])
        return decide(T, prem, gl).kind

    def test_library_rows_agree(self):
        total = 0
        for goal in (f"iso(G, {PB})", f"embeds(G, {S})", f"countable({S})", f"no-finite-quotients({S})",
                     f"co-hopfian({S})", f"linear({S})", f"solvable({S})", f"indecomposable({S})",
                     f"contains-free({PO})", f"perfect({PO})", f"iso({PO}, {S})", f"nilpotent({PO})",
                     f"hyperbolic({PO})", f"iso(G, {PO})"):
            rows, bad, known = self._rows(goal)
            print(f"  {goal}: строк {rows}, значение известно {known}, противоречий {bad}", file=sys.stderr)
            self.assertGreater(rows, 1000, goal)
            self.assertGreater(known, 0, goal)  # у вложений в Sym(G) библиотека знает немного
            self.assertEqual(bad, 0, goal)
            total += known
        self.assertGreater(total, 20000)

    def test_derive(self):
        G = "∀ G : Grp"
        for quant, cond, goal in (
                (G, "", f"embeds(G, {S})"),
                (G, "", f"iso(G, {PB})"),
                (G, "", f"embeds({PB}, {S})"),
                (G, "abelian(G)", f"abelian({PB})"),
                (G, "¬finite(G)", f"¬countable({S})"),
                (G, "¬finite(G)", f"¬residually-finite({S})"),
                (G, "¬finite(G)", f"¬co-hopfian({S})"),
                (G, "¬finite(G)", f"¬linear-c({S})"),
                (G, "finite(G)", f"two-generated({S})"),
                (G, f"solvable({S}), ¬trivial(G), ¬prime-order(G)", "order-p2(G)"),
                (G, f"divisible({S})", "trivial(G)"),
                (G, "", f"embeds({S}, {PO})"),
                (G, "¬cyclic(G)", f"contains-free({PO})"),
                (G, "¬cyclic(G)", f"¬proper-subs-cyclic({PO})"),
                (G, "¬cyclic(G)", f"¬amenable({PO})"),
                (G, "finite(G)", f"hyperbolic({PO})"),
                (G, "finite(G), ¬trivial(G)", f"¬perfect({PO})"),
                (G, "¬finite(G)", f"perfect({PO})"),
                (G, "cyclic(G), exponent-3(G)", f"solvable({PO})"),
                (G, "¬two-primes(G)", f"¬iso({PO}, {S})"),
                (G, "", f"indecomposable({S})"),
                (G, "¬finite(G)", f"¬iso(G, {PO})"),
                (G, f"proper-subs-abelian({S}), ¬trivial(G)", "prime-order(G)"),
                (GHF, "surjective(F)", "iso(pushout(F, F), H)"),
                (GHF, "¬surjective(F)", "¬simple(pushout(F, F))"),
                (GHF, "¬surjective(F)", "¬abelian(pushout(F, F))"),
                (GHF, "fin-pres(pushout(F, F))", "fin-pres(H)"),
                (GHF, "solvable(G)", "solvable(pullback(F, F))"),
                (GHF2, "zero-mor(F), zero-mor(E)", "whole(equalizer(F, E))"),
                (GHF2, "abelian(H)", "abelian(coequalizer(F, E))")):
            self.assertEqual(self._kind(quant, cond, goal), "выводится", (cond, goal))

    def test_false_not_derived(self):
        # Sym∗Sym над бесконечной X совершенна; над C₃ без F₂; Sym(C₄) разрешима; pullback
        # неинъективного F больше X; амальгама над F(X) ≠ Y может быть ≅ Y (свободные бесконечного ранга)
        G = "∀ G : Grp"
        for quant, cond, goal in (
                (G, "¬trivial(G)", f"¬perfect({PO})"),
                (G, "¬trivial(G)", f"contains-free({PO})"),
                (G, "finite(G)", f"¬solvable({S})"),
                (G, "¬finite(G)", f"embeds({PO}, {S})"),
                (G, "", f"two-generated({PO})"),
                (GHF, "", "iso(pullback(F, F), G)"),
                (GHF, "¬surjective(F)", "¬iso(pushout(F, F), H)"),
                (GHF, "two-generated(H)", "two-generated(pushout(F, F))"),
                (GHF2, "injective(F)", "trivial(equalizer(F, E))")):
            self.assertNotEqual(self._kind(quant, cond, goal), "выводится", (cond, goal))


if __name__ == "__main__":
    unittest.main()
