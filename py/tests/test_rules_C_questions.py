"""Пакет 2 (16.11): правила для вопросов человеку (C) пилота 14 и структурные правила «собственные
подгруппы … ⇒ 2-порождена». Вопрос C — запрет: при посылках-литералах выводится отрицание последнего."""
import unittest
from unittest.mock import patch

from algen.etalon import scheme
from algen.logic import Theory, Vocab, decide


def kind(conj):
    from algen import enumerate as E
    v = Vocab.section("grp")
    lits = [x.strip() for x in conj.split(" & ")]
    *prem, last = lits
    goal = last[1:] if last.startswith("¬") else "¬" + last
    g, pr, gl = scheme(v, {"раздел": "grp", "условие": "∀ G : Grp" + (" | " + ", ".join(prem) if prem else ""),
                           "цель": goal})
    terms = {t for a in [gl[0]] + [p[0] for p in pr] for t in a[2:] if not isinstance(t, (str, int, bool))}
    req = sorted({x for t in terms for x in g.requires(t)}, key=str)
    T = Theory(g, grow=1, extra=list(E.relation_atoms(g, list(g.terms))) + ([gl[0]] if gl[0][0] == "r" else []))
    return decide(T, list(pr) + [(("p", p, u), True) for p, u in req], gl).kind


CLOSED = [
    "order-pq(quotient(G, center(G))) & proper-subs-abelian(G) & ¬hopfian(quotient(G, frattini(G)))",
    "abelian(pushout(cayley(G), cayley(G))) & ¬iso(G, pushout(cayley(G), cayley(G)))",
    "prime-order(aut(G)) & primitive(regular-act(G)) & ¬exponent-3(G)",
    "abelian(prod(G, G)) & co-hopfian(G) & fin-gen(G) & ¬embeds(G, torsion(prod(G, G)))",
    "abelian(prod(G, G)) & no-finite-quotients(G) & ¬divisible(torsion(prod(G, G)))",
    "abelian(prod(G, G)) & proper-subs-finite(G) & ¬clt(G) & ¬divisible(torsion(prod(G, G)))",
    "abelian(prod(G, G)) & proper-subs-finite(G) & ¬complemented(torsion(prod(G, G)))",
    # структурные: неабелева без 2-порождения — не все собственные абелевы; конечная — и нильпотентны
    "proper-subs-abelian(G) & ¬abelian(G) & ¬two-generated(G)",
    "finite(G) & proper-subs-nilpotent(G) & ¬nilpotent(G) & ¬two-generated(G)",
    "proper-subs-finite(G) & ¬periodic(G)",
]

# неверны в общем случае: контрпримеры (C₇⋊C₃)² × C₃ (порядок 1323), C₉ × C₉ × C₃, ⊕ₙ ℤ/pⁿ — проверены
# перебором ревьюером 16.11; в таблице (порядки ⩽ 100) их нет, тест защищает лишь от ложного вывода
OPEN = [
    "centerless(frattini(G)) & odd-order(G) & ¬centerless(quotient(G, frattini(G))) & ¬indecomposable(quotient(G, center(G)))",
    "odd-order(G) & perfect(quotient(G, center(G))) & ¬cyclic(frattini(G)) & ¬iso(frattini(G), quotient(G, frattini(G)))",
    "abelian(prod(G, G)) & p-group(G) & residually-finite(torsion(prod(G, G))) & ¬bounded-exponent(G)",
]


class CQuestionsTest(unittest.TestCase):
    def test_closed_by_rules(self):
        from algen import enumerate as E
        with patch.object(E, "FULL_PROPS", True):
            for conj in CLOSED:
                with self.subTest(conj=conj):
                    self.assertEqual(kind(conj), "выводится")

    def test_false_questions_stay_open(self):
        from algen import enumerate as E
        with patch.object(E, "FULL_PROPS", True):
            for conj in OPEN:
                with self.subTest(conj=conj):
                    self.assertEqual(kind(conj), "неизвестно")


if __name__ == "__main__":
    unittest.main()
