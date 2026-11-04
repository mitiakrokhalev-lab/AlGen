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


# --- экземпляры φ(t) по φ(G) ---------------------------------------------

import numpy as np

from algen.logic import App, Var


class Info:
    def __init__(self, sort):
        self.sort = sort


class G2:
    def __init__(self, terms, req=None):
        self.terms = terms
        self._req = req or {}

    def requires(self, t):
        return self._req.get(t, [])


class T2:
    def __init__(self, g, clauses=()):
        self.g, self.var, self.clauses = g, {}, []
        for cl in clauses:
            self.clauses.append([self.lit(a, v) for a, v in cl])

    def lit(self, a, value=True):
        n = self.var.setdefault(a, len(self.var) + 1)
        return n if value else -n

    def solver(self):
        return Solver(name="g4", bootstrap_with=self.clauses)


GV = Var("G")
ZG = App("center", (GV,))
QG = App("quot", (GV,))


class InstForm:
    """База ∀ G; термы G, Z(G), quot(G) (последний требует normal-ish(G))."""

    def __init__(self, table, clauses=(), fixed=(), sort_z="Grp.obj"):
        g = G2({GV: Info("Grp.obj"), ZG: Info(sort_z), QG: Info("Grp.obj")}, {QG: [("ok", GV)]})
        self.sc = type("SC", (), {})()
        self.sc.T = T2(g, clauses)
        self.atoms = [("p", p, t) for t in (GV, ZG, QG) for p in ("a", "b", "c")] + [("p", "ok", GV)]
        self.index = {a: i for i, a in enumerate(self.atoms)}
        self.fixed_lits = list(fixed)
        self.fixed = [2 * self.index[a] + (0 if v else 1) for a, v in fixed]
        m = np.zeros((len(table), 2 * len(self.atoms)), dtype=bool)
        for i, rowv in enumerate(table):
            for a, v in rowv.items():
                m[i, 2 * self.index[a] + (0 if v else 1)] = True
        self.m = m

    def lit(self, j):
        return self.atoms[j // 2], j % 2 == 0

    def lits(self, j):
        return [self.lit(j)]


def irow(form, prem, goal, kind="неизвестно"):
    cols = [2 * form.index[a] for a in prem] + [2 * form.index[goal] + 1]
    return {"_cols": cols, "класс": tuple(map(str, prem + [goal])), "примеров": 1, "вердикт": kind}


class TestInstances(unittest.TestCase):
    def test_instance_folds_when_admissible_and_unrefuted(self):
        f = InstForm([])
        r = irow(f, [("p", "a", ZG)], ("p", "b", ZG))
        C.compress(f, [r])
        self.assertTrue(r["свёрнута"])
        self.assertEqual(r["экземпляр"], {"терм": "center(G)", "вместо": "G"})
        self.assertEqual(C.verify(f, [r]), [])

    def test_refuted_source_keeps_row(self):
        # группа библиотеки с a(G), ¬b(G): R0 = «a ⇒ b» опровергнут, φ(Z(G)) остаётся
        f = InstForm([{("p", "a", GV): True, ("p", "b", GV): False}])
        r = irow(f, [("p", "a", ZG)], ("p", "b", ZG))
        C.compress(f, [r])
        self.assertFalse(r["свёрнута"])

    def test_requires_must_be_derivable(self):
        f = InstForm([])
        r = irow(f, [("p", "a", QG)], ("p", "b", QG))
        C.compress(f, [r])
        self.assertFalse(r["свёрнута"])  # ok(G) не выводится
        f2 = InstForm([], clauses=[[(("p", "ok", GV), True)]])
        r2 = irow(f2, [("p", "a", QG)], ("p", "b", QG))
        C.compress(f2, [r2])
        self.assertTrue(r2["свёрнута"])

    def test_base_hypothesis_must_hold_for_term(self):
        # база «∀ G с c(G)»: Z(G) подходит, только если теория даёт c(Z(G))
        hyp = [(("p", "c", GV), True)]
        f = InstForm([], fixed=hyp)
        r = irow(f, [("p", "a", ZG)], ("p", "b", ZG))
        C.compress(f, [r])
        self.assertFalse(r["свёрнута"])
        f2 = InstForm([], clauses=[[(("p", "c", GV), False), (("p", "c", ZG), True)]], fixed=hyp)
        r2 = irow(f2, [("p", "a", ZG)], ("p", "b", ZG))
        C.compress(f2, [r2])
        self.assertTrue(r2["свёрнута"])

    def test_sort_mismatch_and_mixed_rows_kept(self):
        f = InstForm([], sort_z="Grp.elt")
        r = irow(f, [("p", "a", ZG)], ("p", "b", ZG))
        C.compress(f, [r])
        self.assertFalse(r["свёрнута"])
        f2 = InstForm([])
        r2 = irow(f2, [("p", "a", GV)], ("p", "b", ZG))  # о G и Z(G) — не экземпляр
        C.compress(f2, [r2])
        self.assertFalse(r2.get("экземпляр"))

    def test_facts_not_folded_by_instance(self):
        f = InstForm([])
        r = irow(f, [("p", "a", ZG)], ("p", "b", ZG), "выводится")
        C.compress(f, [r])
        self.assertFalse(r.get("экземпляр"))


class GenForm(InstForm):
    """Многопеременная база: таблица базы G передаётся в form.generic."""

    def __init__(self, gtable, clauses=(), cls=""):
        super().__init__([], clauses)
        props = ["a", "b", "c", "fin"]
        gcol = {p: i for i, p in enumerate(props)}
        gm = np.zeros((len(gtable), 2 * len(props)), dtype=bool)
        for i, rv in enumerate(gtable):
            for p, v in rv.items():
                gm[i, 2 * gcol[p] + (0 if v else 1)] = True
        self.generic = (gm, gcol)
        self.atoms.append(("p", "fin", ZG))
        self.index = {a: i for i, a in enumerate(self.atoms)}


class TestInstancesGeneric(unittest.TestCase):
    def setUp(self):
        import os
        self._cls = os.environ.pop("ALGEN_CLASS", None)

    def tearDown(self):
        import os
        if self._cls is not None:
            os.environ["ALGEN_CLASS"] = self._cls
        else:
            os.environ.pop("ALGEN_CLASS", None)

    def test_generic_unrefuted_folds(self):
        f = GenForm([{"a": True, "b": True}])
        r = irow(f, [("p", "a", ZG)], ("p", "b", ZG))
        C.compress(f, [r])
        self.assertTrue(r["свёрнута"])

    def test_generic_refuted_kept(self):
        f = GenForm([{"a": True, "b": False}])
        r = irow(f, [("p", "a", ZG)], ("p", "b", ZG))
        C.compress(f, [r])
        self.assertFalse(r["свёрнута"])

    def test_class_needs_term_in_class_and_class_rows(self):
        import os
        os.environ["ALGEN_CLASS"] = "fin"
        # контрпример к R0 — бесконечная группа: в классе «fin» R0 не опровергнут
        tbl = [{"a": True, "b": False, "fin": False}]
        f = GenForm(tbl)
        r = irow(f, [("p", "a", ZG)], ("p", "b", ZG))
        C.compress(f, [r])
        self.assertFalse(r["свёрнута"])  # fin(Z(G)) не выводится — Z(G) может быть вне класса
        f2 = GenForm(tbl, clauses=[[(("p", "fin", ZG), True)]])
        r2 = irow(f2, [("p", "a", ZG)], ("p", "b", ZG))
        C.compress(f2, [r2])
        self.assertTrue(r2["свёрнута"])


class TestCopies(unittest.TestCase):
    def test_class_copies_follow_representative(self):
        """Контрапозиции — копии класса: свёрнута копия ровно тогда, когда
        свёрнут представитель, и источники у неё те же (не сам представитель)."""
        f = FakeForm(ATOMS, [["-a", "b"]])
        q1 = row(f, ["b"], "c", n=5)
        q2 = row(f, ["a"], "c", n=1)
        q2c = dict(q2, _cols=list(reversed(q2["_cols"])), примеров=99)  # та же строка класса, другая поддержка
        rep = C.compress(f, [q1, q2, q2c])
        # класс q2 интереснее (99 примеров у копии): он раньше q1 и остаётся
        self.assertFalse(q2["свёрнута"] or q2c["свёрнута"])
        self.assertEqual(C.verify(f, rep), [])
        q2c["примеров"] = 0
        rep = C.compress(f, [q1, q2, q2c])
        self.assertTrue(q2["свёрнута"] and q2c["свёрнута"])
        self.assertEqual(q2c["следует из"], [q1["№"]])
        self.assertEqual(C.verify(f, rep), [])
        C.reopen(rep, [q1["№"]])
        self.assertFalse(q2["свёрнута"] or q2c["свёрнута"])


class TestRegress(unittest.TestCase):
    def test_regress_clean_and_catches_loss(self):
        rng = random.Random(3)
        for _ in range(50):
            cl = [[rng.choice(["", "-"]) + rng.choice(ATOMS) for _ in range(2)] for _ in range(rng.randint(0, 4))]
            f = FakeForm(ATOMS, cl)
            rows = []
            for _ in range(rng.randint(1, 8)):
                prem = rng.sample(ATOMS, rng.randint(1, 3))
                goal = rng.choice([a for a in ATOMS if a not in prem])
                rows.append(row(f, prem, goal, rng.choice(["неизвестно", "выводится", "опровергается"]), rng.randint(0, 5)))
            before = copy.deepcopy(rows)
            C.compress(f, rows)
            self.assertEqual(C.regress(before, rows), [])
            self.assertEqual(C.regress([C.digest(r) for r in before], rows), [])
        self.assertTrue(C.regress(before, rows[:-1]) or len(rows) == 0)
        rows[0]["вердикт"] = "выводится" if rows[0]["вердикт"] != "выводится" else "неизвестно"
        self.assertTrue(C.regress(before, rows))
        self.assertTrue(C.regress([C.digest(r) for r in before], rows))


class TestGenericFilterClass(unittest.TestCase):
    """enumerate.generic_filter при ALGEN_CLASS: условие о терме снимается,
    только если теория выводит, что терм в классе (дыра 4.11)."""

    def setUp(self):
        import os
        self.env = {k: os.environ.pop(k, None) for k in ("ALGEN_CLASS", "ALGEN_COMPRESS")}

    def tearDown(self):
        import os
        for k, v in self.env.items():
            os.environ.pop(k, None)
            if v is not None:
                os.environ[k] = v

    def run_filter(self, clauses, cls):
        import os
        from algen import enumerate as E
        if cls:
            os.environ["ALGEN_CLASS"] = cls
        f = GenForm([{"a": True, "b": True}], clauses=clauses)  # R0 «a ⇒ b» не опровергнут
        ia, ib = f.index[("p", "a", ZG)], f.index[("p", "b", ZG)]
        mins = {((2 * ia,), 2 * ib): 1}
        return E.generic_filter(f, mins), f

    def test_without_class_unchanged(self):
        out, f = self.run_filter([], "")
        self.assertEqual(out, {})  # снято, как и раньше

    def test_class_term_not_in_class_kept(self):
        out, f = self.run_filter([], "fin")
        self.assertEqual(len(out), 1)
        self.assertEqual(f.generic_kept_class, 1)

    def test_class_term_in_class_dropped(self):
        out, f = self.run_filter([[(("p", "fin", ZG), True)]], "fin")
        self.assertEqual(out, {})


class TestAcross(unittest.TestCase):
    def test_fold_across_schemes(self):
        from algen import compress_base as B
        f = FakeForm(ATOMS, [["-a", "b"]])
        T = f.sc.T
        name2lit = {a: (a, True) for a in ATOMS} | {"¬" + a: (a, False) for a in ATOMS}
        qs = [{"id": "S1:x", "№": "x", "запрет": ["b", "¬c"], "примеров": 5},
              {"id": "S2:y", "№": "y", "запрет": ["a", "¬c"], "примеров": 1},
              {"id": "S3:x", "№": "x", "запрет": ["b", "¬c"], "примеров": 5},
              {"id": "S3:z", "№": "z", "запрет": ["d", "¬e"], "примеров": 1},
              {"id": "S4:w", "№": "w", "запрет": ["q", "¬e"], "примеров": 0}]
        kept, folded, why, enc, fx = B.fold_across(T, name2lit, [], qs)
        self.assertEqual(sorted(kept), ["S1:x", "S3:z", "S4:w"])
        self.assertEqual(folded["S2:y"], ["S1:x"])
        self.assertEqual(folded["S3:x"], ["S1:x"])
        self.assertEqual(why["S4:w"], "нет литерала в каркасе")
        self.assertEqual(B.verify_across(T, enc, fx, kept, folded), [])
        self.assertTrue(B.verify_across(T, enc, fx, kept, dict(folded, **{"S2:y": ["S3:z"]})))
