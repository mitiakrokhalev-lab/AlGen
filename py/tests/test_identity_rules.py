"""Тождества термов (кандидаты claude-tool-01): аксиомы «⩽ ⇒ ↪», «= ⇒ ↪», «= ⇒ ≅» и правила
data/new/grp.json, после которых кандидаты выводятся; контроль — неверные в общем случае кандидаты
(перекос библиотеки) по-прежнему не выводятся."""
import unittest
from unittest.mock import patch

from algen.etalon import scheme
from algen.logic import Theory, Vocab, decide


def kind(goal, premises=(), decl="∀ G : Grp"):
    from algen import enumerate as E
    v = Vocab.section("grp")
    decl = decl + (" | " + ", ".join(premises) if premises else "")
    g, prem, gl = scheme(v, {"раздел": "grp", "условие": decl, "цель": goal})
    terms = [t for t in gl[0][2:] if not isinstance(t, (str, int, bool))]
    req = sorted({x for t in terms for x in g.requires(t)}, key=str)
    extra = list(E.relation_atoms(g, list(g.terms))) + ([gl[0]] if gl[0][0] == "r" else [])
    T = Theory(g, grow=1, extra=extra)
    return decide(T, list(prem) + [(("p", p, u), True) for p, u in req], gl).kind


DERIVED = [
    # аксиомы: подгруппы одной группы
    ("embeds(comm(G, frattini(G), frattini(G)), frattini(G))", ()),
    ("embeds(comm(G, commutator(G), commutator(G)), commutator(G))", ()),
    ("embeds(ulm(G), frattini(G))", ("abelian(G)",)),
    # правила
    ("embeds(center(sym(G)), G)", ()),
    ("trivial(nc(G, center(G)))", ()),
    ("trivial(nc(G, ulm(G)))", ("abelian(G)",)),
    ("trivial(frattini(sym(G)))", ()),
    ("embeds(ab(sym(G)), sym(G))", ()),
    ("embeds(quotient(G, commutator(G)), sym(G))", ()),
    ("embeds(ab(G), sym(G))", ()),
    ("embeds(inn(G), sym(G))", ()),
    ("embeds(quotient(G, center(G)), aut(G))", ()),
    ("embeds(center(wreath(G, G)), G)", ()),
    ("embeds(G, inn(wreath(G, G)))", ()),
    ("embeds(center(G), prod-sub(G, G, center(G), center(G)))", ()),
    ("trivial(ulm(quotient(G, ulm(G))))", ("abelian(G)",)),
    ("embeds(quotient(G, ulm(G)), profinite(G))", ("abelian(G)",)),
    # аксиомы «= ⇒ ↪», «= ⇒ ≅» (нормальное замыкание нормальной подгруппы — она сама)
    ("embeds(normal-closure(G, center(G)), center(G))", ()),
    ("iso(normal-closure(G, center(G)), center(G))", ()),
    # прочие правила пакета прямо
    ("embeds(aut(G), sym(G))", ()),
    ("embeds(frattini(G), prod-sub(G, G, center(G), frattini(G)))", ()),
    ("embeds(G, aut(wreath(G, G)))", ()),
    ("embeds(quotient(sym(G), commutator(sym(G))), sym(G))", ()),
]

# сплетение двух разных групп: посылка X ≠ 1 нужна (X = 1, Y = C₂: W ≅ C₂, Z(W) = C₂ ⋠ 1)
TWO = "∀ G : Grp; ∀ H : Grp"
WREATH = [
    "embeds(center(wreath(G, H)), center(G))",
    "embeds(center(wreath(G, H)), G)",
    "embeds(H, quotient(wreath(G, H), center(wreath(G, H))))",
    "embeds(H, inn(wreath(G, H)))",
    "embeds(H, aut(wreath(G, H)))",
]

# неверны в общем случае (контрпример в скобках): правила их выводить не должны
NOT_DERIVED = [
    ("whole(ulm(ulm(G)))", ("abelian(G)",)),                  # обобщённая группа Прюфера H_{ω+1}
    ("trivial(nc(G, commutator(G)))", ()),                    # S₃
    ("trivial(nc(G, frattini(G)))", ()),                      # D₁₆
    ("iso(profinite(G), profinite(profinite(G)))", ()),       # ⊕_ω C₂
    ("embeds(inn(G), freeprod(G, quotient(aut(G), inn(G))))", ()),  # Q₈ (Курош)
]


class IdentityRulesTest(unittest.TestCase):
    def test_candidates_become_derivable(self):
        from algen import enumerate as E
        with patch.object(E, "FULL_PROPS", True):  # полный класс, как в таблицах (ALGEN_SIZE)
            for goal, prem in DERIVED:
                with self.subTest(goal=goal):
                    self.assertEqual(kind(goal, prem), "выводится")

    def test_wreath_rules_need_nontrivial_base(self):
        from algen import enumerate as E
        with patch.object(E, "FULL_PROPS", True):
            for goal in WREATH:
                with self.subTest(goal=goal):
                    self.assertEqual(kind(goal, ("¬trivial(G)",), decl=TWO), "выводится")
                    self.assertEqual(kind(goal, (), decl=TWO), "неизвестно")

    def test_false_candidates_stay_open(self):
        from algen import enumerate as E
        with patch.object(E, "FULL_PROPS", True):
            for goal, prem in NOT_DERIVED:
                with self.subTest(goal=goal):
                    self.assertEqual(kind(goal, prem), "неизвестно")


if __name__ == "__main__":
    unittest.main()
