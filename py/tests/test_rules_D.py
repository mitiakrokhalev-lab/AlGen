"""Пакет D (13.11): правила для атомов таблицы G без значений во всех строках (аудит сборки
42525138952): проекция X → X/N инъективна ⇔ N = 1; BS(m, n) 2-порождена; композиция
сохраняет инъективность, сюръективность и внутренность. Задуманное выводится, похожие
ложные или недоказанные утверждения — нет."""
import unittest

from algen.etalon import scheme
from algen.logic import Theory, Vocab, decide


class RulesDTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.v = Vocab.section("grp")

    def _kind(self, cond, goal):
        g, prem, gl = scheme(self.v, {"раздел": "grp", "условие": cond, "цель": goal})
        T = Theory(g, grow=1, extra=[a for a, _ in prem + [gl] if a[0] == "r"])
        return decide(T, prem, gl).kind

    def test_derive(self):
        for cond, goal in (
                ("∀ G : Grp | trivial(center(G))", "injective(proj(G, center(G)))"),
                ("∀ G : Grp | trivial(center(G))", "iso(proj(G, center(G)))"),
                ("∀ G : Grp | ¬trivial(commutator(G))", "¬iso(proj(G, commutator(G)))"),
                ("∀ G : Grp | injective(proj(G, frattini(G)))", "trivial(frattini(G))"),
                ("∀ G : Grp | finite(G)", "two-generated(bs(ord(G), ord(G)))"),
                ("∀ G : Grp", "iso(compose(id-mor(G), id-mor(G)))"),
                ("∀ G : Grp", "inner-aut(compose(id-mor(G), id-mor(G)))"),
                ("∀ G : Grp; ∀ F : Mor(G, G) | injective(compose(F, F))", "injective(F)"),
                ("∀ G : Grp; ∀ F : Mor(G, G) | surjective(compose(F, F))", "surjective(F)")):
            self.assertEqual(self._kind(cond, goal), "выводится", (cond, goal))

    def test_false_not_derived(self):
        # Z(G) бывает нетривиален; BS(n, n) при n = ∞ не определена; ранг тривиальной группы 0,
        # BS(0, 0) = F₂ гиперболична; инъективный эндоморфизм ℤ (x ↦ 2x) не сюръективен, и его квадрат тоже
        for cond, goal in (
                ("∀ G : Grp", "injective(proj(G, center(G)))"),
                ("∀ G : Grp", "two-generated(bs(ord(G), ord(G)))"),
                ("∀ G : Grp | trivial(G)", "¬hyperbolic(bs(rank(G), rank(G)))"),
                ("∀ G : Grp; ∀ F : Mor(G, G) | injective(F)", "surjective(compose(F, F))"),
                ("∀ G : Grp; ∀ F : Mor(G, G) | injective(compose(F, F))", "surjective(F)")):
            self.assertNotEqual(self._kind(cond, goal), "выводится", (cond, goal))


if __name__ == "__main__":
    unittest.main()
