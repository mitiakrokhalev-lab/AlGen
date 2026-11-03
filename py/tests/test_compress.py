"""Сжатие выдачи: базис относительно теории без дыр (docs/класс-перебора.md,
«Сжатие выдачи: правила»)."""
import copy
import random
import unittest

from pysat.solvers import Solver

from algen import compress as C


class FakeT:
    def __init__(self, atoms, clauses):
        self.v = {a: i + 1 for i, a in enumerate(atoms)}
        self.clauses = [[(1 if x[0] != "-" else -1) * self.v[x.lstrip("-")] for x in cl] for cl in clauses]

    def lit(self, a, value=True):
        return self.v[a] if value else -self.v[a]

    def solver(self):
        return Solver(name="g4", bootstrap_with=self.clauses)


class FakeForm:
    def __init__(self, atoms, clauses, fixed=()):
        self.atoms = list(atoms)
        self.sc = type("SC", (), {})()
        self.sc.T = FakeT(atoms, clauses)
        self.fixed_lits = list(fixed)

    def lits(self, j):
        return [(self.atoms[j // 2], j % 2 == 0)]


def row(form, prem, goal, kind="неизвестно", n=1):
    """prem: список атомов-посылок (верны), goal: атом (верен)."""
    ix = {a: i for i, a in enumerate(form.atoms)}
    cols = [2 * ix[a] for a in prem] + [2 * ix[goal] + 1]
    return {"_cols": cols, "посылки": prem, "цель": goal, "класс": tuple(sorted(prem)) + ("¬" + goal,),
            "примеров": n, "вердикт": kind}


ATOMS = ["a", "b", "c", "d", "e"]


class TestCompress(unittest.TestCase):
    def test_question_folds_through_theory_and_kept_question(self):
        f = FakeForm(ATOMS, [["-a", "b"]])  # теория: a ⇒ b
        q1, q2 = row(f, ["b"], "c", n=5), row(f, ["a"], "c", n=1)
        rep = C.compress(f, [q2, q1])
        self.assertFalse(q1["свёрнута"])
        self.assertTrue(q2["свёрнута"])
        self.assertEqual(q2["следует из"], [q1["№"]])
        self.assertEqual(C.verify(f, rep), [])

    def test_order_matters_and_nothing_removed(self):
        f = FakeForm(ATOMS, [["-a", "b"]])
        q1, q2 = row(f, ["b"], "c", n=1), row(f, ["a"], "c", n=5)  # a ⇒ c интереснее
        before = copy.deepcopy([q1, q2])
        rep = C.compress(f, [q1, q2])
        self.assertEqual(len(rep), 2)
        self.assertFalse(q1["свёрнута"] or q2["свёрнута"])  # b ⇒ c не следует из a ⇒ c
        for old, new in zip(before, rep):
            for k, v in old.items():
                self.assertEqual(new[k], v, "прежние поля не меняются")

    def test_facts_basis_without_theory(self):
        f = FakeForm(ATOMS, [["-a", "b"], ["-b", "c"]])
        f1, f2, f3 = row(f, ["a"], "b", "выводится", 3), row(f, ["b"], "c", "выводится", 2), row(f, ["a"], "c", "выводится", 1)
        C.compress(f, [f1, f2, f3])
        self.assertFalse(f1["свёрнута"] or f2["свёрнута"])
        self.assertTrue(f3["свёрнута"])
        self.assertEqual(sorted(f3["следует из"]), sorted([f1["№"], f2["№"]]))

    def test_facts_never_background_for_questions_and_vice_versa(self):
        f = FakeForm(ATOMS, [])
        fact, q = row(f, ["a"], "b", "выводится", 9), row(f, ["a", "d"], "b", "неизвестно", 1)
        C.compress(f, [fact, q])
        self.assertFalse(q["свёрнута"])

    def test_solver_no_answer_keeps_row(self):
        f = FakeForm(ATOMS, [["-a", "b"]])
        q1, q2 = row(f, ["b"], "c", n=5), row(f, ["a"], "c", n=1)
        orig = C._solve
        C._solve = lambda s, a: None
        try:
            C.compress(f, [q1, q2])
        finally:
            C._solve = orig
        self.assertFalse(q1["свёрнута"] or q2["свёрнута"])

    def test_question_from_theory_alone_is_flagged_not_folded(self):
        f = FakeForm(ATOMS, [["-a", "b"]])
        q = row(f, ["a"], "b")
        C.compress(f, [q])
        self.assertFalse(q["свёрнута"])
        self.assertIn("ОШИБКА сжатия", q)

    def test_reopen_transitive_and_refuted_excluded(self):
        f = FakeForm(ATOMS, [["-a", "b"], ["-d", "a"]])
        q1, q2, q3 = row(f, ["b"], "c", n=9), row(f, ["a"], "c", n=5), row(f, ["d", "e"], "c", n=1)
        C.compress(f, [q1, q2, q3])
        self.assertTrue(q2["свёрнута"] and q3["свёрнута"])
        back = C.reopen([q1, q2, q3], [q1["№"]])
        self.assertEqual(back, {q2["№"], q3["№"]})
        C.compress(f, [q1, q2, q3], refuted=[q1["№"]])
        self.assertTrue(q1.get("опровергнут"))
        self.assertFalse(q2["свёрнута"])  # без q1 a ⇒ c не следует

    def test_verify_catches_tampering(self):
        f = FakeForm(ATOMS, [["-a", "b"]])
        q1, q2, q3 = row(f, ["b"], "c", n=5), row(f, ["a"], "c", n=1), row(f, ["d"], "e", n=7)
        rep = C.compress(f, [q1, q2, q3])
        self.assertEqual(C.verify(f, rep), [])
        q2["следует из"] = [q3["№"]]
        self.assertTrue(C.verify(f, rep))

    def test_random_soundness(self):
        """Случайные теории и вопросы: каждый свёрнутый следует из своих
        источников (проверка новым решателем), источники не свёрнуты."""
        rng = random.Random(1)
        for _ in range(200):
            cl = [[rng.choice(["", "-"]) + rng.choice(ATOMS) for _ in range(2)] for _ in range(rng.randint(0, 4))]
            f = FakeForm(ATOMS, cl)
            rows = []
            for _ in range(rng.randint(1, 8)):
                prem = rng.sample(ATOMS, rng.randint(1, 3))
                goal = rng.choice([a for a in ATOMS if a not in prem])
                rows.append(row(f, prem, goal, rng.choice(["неизвестно", "выводится"]), rng.randint(0, 5)))
            rows = list({r["класс"]: r for r in rows}.values())
            C.compress(f, rows)
            self.assertEqual(C.verify(f, rows), [])


if __name__ == "__main__":
    unittest.main()
