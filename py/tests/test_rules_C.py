"""Пакет C (9.11): правила о X × Y и квадрате X × X, кручении T(X × X), Φ(X) и X/Φ(X), подгруппе Ульма,
централизаторе, ядре подгруппы, нормальном замыкании и ядре гомоморфизма. Строки библиотеки
согласны с теорией, задуманное выводится, похожие ложные утверждения не выводятся."""
import unittest

from algen.etalon import scheme
from algen.library import Library, Search
from algen.logic import Theory, Vocab, decide

# цель → наименьшее число строк библиотеки, где значение цели известно (все факты строки
# сверяются с теорией, так что проверяются и атомы, которых нет в цели)
AGREE = {
    "proper-subs-cyclic(prod(G, G))": 60,
    "two-generated(prod(G, G))": 15,
    "dedekind(prod(G, G))": 90,
    "prime-orders(prod(G, G))": 25,
    "co-hopfian(prod(G, G))": 75,
    "no-finite-quotients(prod(G, G))": 35,
    "two-primes(prod(G, G))": 15,
    "locally-cyclic(prod(G, G))": 90,
    "proper-subs-abelian(prod(inn(G), inn(G)))": 450,
    "trivial(torsion(prod(G, G)))": 90,
    "proper-subs-cyclic(torsion(prod(G, G)))": 70,
    "embeds(torsion(prod(G, G)), G)": 90,
    "complemented(torsion(G))": 800,
    "trivial(frattini(quotient(G, frattini(G))))": 1200,
    "cyclic(quotient(G, frattini(G)))": 1400,
    "p-group(quotient(G, frattini(G)))": 1300,
    "prime-index(frattini(G))": 1200,
    "complemented(commutator(G))": 850,
}


class RulesCTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.lib = Library()
        cls.v = Vocab.section("grp")

    def _rows(self, goal):
        g, prem, gl = scheme(self.v, {"раздел": "grp", "условие": "∀ G : Grp", "цель": goal})
        T = Theory(g, grow=1, extra=[gl[0]] if gl[0][0] == "r" else [])
        S = Search(g, T, self.lib)
        s = T.solver()
        rows = bad = known = 0
        try:
            for env in S._assign(0, {}):
                facts, _ = S.facts(env)
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

    def _kind(self, cond, goal):
        g, prem, gl = scheme(self.v, {"раздел": "grp", "условие": cond, "цель": goal})
        T = Theory(g, grow=1, extra=[a for a, _ in prem + [gl] if a[0] == "r"])
        return decide(T, prem, gl).kind

    def test_library_rows_agree(self):
        for goal, least in AGREE.items():
            rows, bad, known = self._rows(goal)
            self.assertEqual(bad, 0, goal)
            self.assertGreaterEqual(known, least, (goal, rows, known))

    def test_derive(self):
        for cond, goal in (
                ("free-abelian(prod(G, G))", "free-abelian(G)"),
                ("two-generated(prod(G, G))", "two-generated(G)"),
                ("fin-pres(G)", "fin-pres(prod(G, G))"),
                ("comp-series(prod(G, G))", "comp-series(G)"),
                ("hyperbolic(prod(G, G))", "finite(G)"),
                ("proper-subs-abelian(prod(inn(G), inn(G)))", "abelian(inn(G))"),
                ("proper-subs-cyclic(prod(G, G)), ¬trivial(G)", "prime-order(G)"),
                ("dedekind(prod(G, G))", "abelian(G)"),
                ("abelian(G), two-generated(prod(G, G))", "cyclic(G)"),
                ("prime-orders(prod(G, G))", "p-group(G)"),
                ("co-hopfian(G), embeds(prod(G, G), G)", "trivial(G)"),
                ("abelian(prod(G, G)), indecomposable(torsion(prod(G, G)))", "torsion-free(G)"),
                ("abelian(prod(G, G)), cyclic(torsion(prod(G, G)))", "torsion-free(G)"),
                ("abelian(prod(G, G)), finite(torsion(prod(G, G))), embeds(torsion(prod(G, G)), G)",
                 "trivial(torsion(prod(G, G)))"),
                ("abelian(prod(G, G)), proper-subs-finite(torsion(prod(G, G)))", "finite(torsion(prod(G, G)))"),
                ("nilpotent(quotient(G, frattini(G)))", "abelian(quotient(G, frattini(G)))"),
                ("fin-gen(G), cyclic(quotient(G, frattini(G)))", "cyclic(G)"),
                ("finite(G), nilpotent(G), complemented(commutator(G))", "abelian(G)"),
                ("maximal(frattini(G))", "prime-index(frattini(G))"),
                ("abelian(G), divisible(G)", "whole(ulm(G))"),
                ("abelian(G), fin-gen(G)", "complemented(torsion(G))"),
                ("simple(G), ¬whole(frattini(G))", "trivial(core(G, frattini(G)))"),
                ("abelian(commutator(G))", "le(commutator(G), centralizer(G, commutator(G)))"),
                ("whole(centralizer(G, commutator(G)))", "central(commutator(G))"),
                ("simple(G), ¬trivial(center(G))", "whole(normal-closure(G, center(G)))")):
            self.assertEqual(self._kind("∀ G : Grp | " + cond, goal), "выводится", (cond, goal))

    def test_false_not_derived(self):
        # C₂ × C₂: квадрат нециклической дедекиндовой, ℤ × ℤ: не 2-порождённость у абелевой без цикличности;
        # A₅ × A₅ 2-порождена при нециклической A₅; ℚ: X × X ↪ X без кохопфовости; ℤ: X × X не гиперболична,
        # но ℤ гиперболична; C₂: кручение ℤ × C₂ — дополняемо, но не 1
        for cond, goal in (
                ("two-generated(prod(G, G))", "cyclic(G)"),
                ("hyperbolic(G)", "hyperbolic(prod(G, G))"),
                ("embeds(prod(G, G), G)", "trivial(G)"),
                ("dedekind(prod(G, G))", "cyclic(G)"),
                ("abelian(prod(G, G)), embeds(torsion(prod(G, G)), G)", "trivial(torsion(prod(G, G)))"),
                ("proper-subs-cyclic(prod(G, G))", "trivial(G)"),
                ("fin-gen(G), abelian(G)", "trivial(torsion(G))"),
                ("abelian(G)", "complemented(torsion(G))"),
                ("cyclic(quotient(G, frattini(G)))", "cyclic(G)"),
                ("abelian(G)", "trivial(ulm(G))"),
                ("abelian(commutator(G))", "central(commutator(G))"),
                # потеря посылок «конечна» / «к. п.» в правилах о Φ: у бесконечных без них ложно
                ("p-group(quotient(G, frattini(G)))", "p-group(G)"),
                ("complemented(frattini(G))", "trivial(frattini(G))"),
                ("two-generated(quotient(G, frattini(G)))", "two-generated(G)")):
            self.assertNotEqual(self._kind("∀ G : Grp | " + cond, goal), "выводится", (cond, goal))


if __name__ == "__main__":
    unittest.main()
