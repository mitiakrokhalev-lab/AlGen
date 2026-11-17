"""algen.knowledge (ALGEN_KNOWLEDGE=1): виды неизвестных условий A/B/C/R и корни недостающих знаний.

Виды и счётчики строк сверяются с независимым скалярным оракулом GPT (test_value_classify.oracle)
и с его C++-классификатором (value_classify.PreparedValues) — три реализации одного определения.
Корни — со скалярным пересчётом по строкам. Сквозной прогон: без флага выдача прежняя, с флагом
к ней только добавляются поля."""
import io
import json
import shutil
import unittest
from types import SimpleNamespace
from unittest.mock import patch

import numpy as np

from algen import enumerate as E
from algen import knowledge as K
from algen.logic import Var

from test_value_classify import fake, oracle, queries_for

KIND = ("C", "A", "B", "R")


def scalar_roots(form, kn, cols):
    """Корни по определению: строки без ложных литералов; у A — неизвестная клетка строк с одним
    неизвестным, у B — все неизвестные клетки строк с ⩾ 2."""
    lits = kn.expand(cols)
    single, multi = [], []
    for r in range(form.m.shape[0]):
        if any(form.m[r, c ^ 1] for c in lits):
            continue
        missing = [c for c in lits if not form.m[r, c]]
        (single if len(missing) == 1 else multi if len(missing) > 1 else []).append((r, missing))
    cells = single if single else multi
    return {(kn.pattern[c // 2], ", ".join(kn._object(r, v) for v in kn.avars[c // 2]) or "—")
            for r, missing in cells for c in missing}


def var_form(rows, objects, synth=()):
    """Свойства a, b, c, d переменной G; строки — группы objects[r] (synth — построенные)."""
    G = Var("G")
    f = fake(rows, [("p", x, G) for x in "abcd"])
    f.lib = SimpleNamespace(obj={o: ({"синтез": True} if o in synth else {}) for o in set(objects)})
    f._image = lambda r, t: ("obj", objects[r])
    return f


class KindsTest(unittest.TestCase):
    def test_kinds_and_row_counts_match_scalar_oracle(self):
        rng = np.random.default_rng(16112026)
        for nr in (0, 1, 2, 7, 63, 64, 65, 129):
            raw = rng.integers(0, 3, size=(nr, 4))
            form = fake([[None if x == 2 else bool(x) for x in row] for row in raw], [("p", p, "G") for p in "abcd"])
            kn = K.Knowledge(form)
            qs = list(queries_for(4))
            kinds, singles, multis, refuters = oracle(form, qs)[:4]
            for i, (prem, goal) in enumerate(qs):
                kind, n1, n2, n0, _ids = kn.classify(list(prem) + [goal ^ 1])
                with self.subTest(rows=nr, q=(prem, goal)):
                    self.assertEqual((kind, n1, n2, n0),
                                     (KIND[kinds[i]], int(singles[i]), int(multis[i]), int(refuters[i])))

    def test_kinds_match_native_classifier(self):
        if shutil.which("g++") is None:
            self.skipTest("нет g++ для value_classify")
        from algen.value_classify import PreparedValues
        from test_value_classify import packed
        rng = np.random.default_rng(5)
        raw = rng.integers(0, 3, size=(130, 4))
        form = fake([[None if x == 2 else bool(x) for x in row] for row in raw], [("p", p, "G") for p in "abcd"])
        kn = K.Knowledge(form)
        p = packed(form, queries_for(4))
        decoded = list(p)
        cursor = 0
        for b in PreparedValues(form).iter_batches(p, 1000):
            for i, (prem, goal) in enumerate(decoded[cursor:cursor + len(b.keys)]):
                kind, n1, n2, n0, _ = kn.classify(list(prem) + [goal ^ 1])
                self.assertEqual((kind, n1, n2, n0), (KIND[b.kinds[i]], int(b.single[i]), int(b.multi[i]),
                                                      int(b.refuting[i])))
            cursor += len(b.keys)
        self.assertEqual(cursor, len(decoded))

    def test_pairs_expand_and_negated_pair_is_an_error(self):
        atoms = [("p", "p", "A"), ("p", "p", "B"), ("p", "q", "G")]
        for row in [(True, None, False), (False, None, False), (None, None, False), (True, True, None)]:
            form = fake([row], atoms)
            E.add_pairs(form, [("A", "B")])
            kn = K.Knowledge(form)
            for q in [((6,), 4), ((8,), 4), ((6,), 5), ((0, 6), 4)]:
                kinds, singles, multis, refuters = oracle(form, [q])[:4]
                kind, n1, n2, n0, _ = kn.classify(list(q[0]) + [q[1] ^ 1])
                self.assertEqual((kind, n1, n2, n0),
                                 (KIND[kinds[0]], int(singles[0]), int(multis[0]), int(refuters[0])), (row, q))
            self.assertTrue(kn.classify([7, 5])[0].startswith("ОШИБКА"))
        # противоречивый запрет — ошибка разметки, не вид
        self.assertTrue(K.Knowledge(fake([(None, None, None)])).classify([0, 1])[0].startswith("ОШИБКА"))


class RootsTest(unittest.TestCase):
    def test_roots_match_scalar_definition(self):
        rng = np.random.default_rng(7)
        objects = ["g0", "g1", "×1", "g0", "×2", "g3", "g1", "g4"] * 4
        raw = rng.integers(0, 3, size=(len(objects), 4))
        form = var_form([[None if x == 2 else bool(x) for x in row] for row in raw], objects, synth={"×1", "×2"})
        kn = K.Knowledge(form)
        for prem, goal in queries_for(4, 2):
            cols = list(prem) + [goal ^ 1]
            kind, _n1, _n2, _n0, ids = kn.classify(cols)
            got = {kn.root_name(x) for x in ids}
            want = scalar_roots(form, kn, cols) if kind in ("A", "B") else set()
            self.assertEqual(got, want, (prem, goal, kind))
            # построенные произведения — один объект «×» (задача-правило)
            self.assertFalse({o for _p, o in got} & {"×1", "×2"})

    def test_hitting_is_a_valid_cover(self):
        rng = np.random.default_rng(3)
        for _ in range(40):
            sets = [np.unique(rng.integers(0, 12, size=rng.integers(0, 5))) for _ in range(rng.integers(1, 15))]
            n = K.hitting(sets)
            nonempty = [set(s.tolist()) for s in sets if len(s)]
            if not nonempty:
                self.assertEqual(n, 0)
                continue
            self.assertGreaterEqual(n, 1)
            self.assertLessEqual(n, len(nonempty))
            # не меньше точного минимума (перебор по размеру)
            from itertools import combinations
            universe = sorted(set().union(*nonempty))
            best = next(k for k in range(1, len(universe) + 1)
                        if any(all(set(c) & s for s in nonempty) for c in combinations(universe, k)))
            self.assertGreaterEqual(n, best)
        self.assertEqual(K.hitting([np.array([1, 2]), np.array([2, 3]), np.array([4])]), 2)
        self.assertEqual(K.hitting([np.array([], dtype=np.int64)]), 0)


class AnnotateTest(unittest.TestCase):
    def test_annotate_fields_summary_and_kept_split(self):
        # строки 0, 1 — g0, g1; строка 2 — построенное произведение; 3 — g3
        form = var_form([(True, None, None, None), (True, None, None, None), (None, True, False, None),
                         (False, False, False, None)], ["g0", "g1", "×", "g3"], synth={"×"})
        report = [
            {"вердикт": "неизвестно", "_cols": [0, 5], "№": 1, "запрет": ["a(G)", "¬c(G)"], "примеров": 2},  # A
            {"вердикт": "неизвестно", "_cols": [2, 1], "№": 2, "свёрнута": True, "запрет": ["b(G)", "¬a(G)"]},  # A
            {"вердикт": "неизвестно", "_cols": [4, 1], "№": 3, "запрет": ["c(G)", "¬a(G)"], "примеров": 0},  # C
            {"вердикт": "неизвестно", "_cols": [7, 6], "№": 4, "запрет": ["d(G)", "¬d(G)"]},  # противоречив
            {"вердикт": "выводится", "_cols": [0, 4], "№": 5},
        ]
        kn = K.annotate(form, report)
        self.assertEqual([r.get("вид") for r in report], ["A", "A", "C", "ОШИБКА: противоречивый запрет", None])
        self.assertEqual(report[0]["корни"], ["a(G) у ×", "c(G) у g0", "c(G) у g1"])
        self.assertEqual(report[0]["корней"], 3)
        self.assertEqual(report[0]["строк"], {"с одним неизвестным": 3, "с несколькими": 0})
        self.assertNotIn("вид", report[4])
        s = kn["сводка"]
        allu, kept = s["все неизвестные"], s["оставленные после сжатия"]
        self.assertEqual(allu["по видам"], {"A": 2, "C": 1, "ОШИБКА: противоречивый запрет": 1})
        self.assertEqual((allu["корней знаний всего"], allu["из них значений записанных групп"],
                          allu["из них правил для произведений (шаблон × «×»)"]), (3, 2, 1))
        self.assertEqual(allu["корней, чтобы затронуть все условия A/B (жадно)"], 1)  # «a(G) у ×» — в обоих
        self.assertEqual((kept["запретов"], kept["строк"], kept["вопросов человеку (C)"], kept["ждут знаний (A + B)"]),
                         (3, 3, 1, 1))
        self.assertEqual(s["вопросы человеку"], [{"№": 3, "запрет": "c(G) & ¬a(G)", "примеров": 0}])
        self.assertEqual(s["очередь знаний"][0]["запретов"], 1)
        self.assertEqual({q["что"] for q in s["очередь знаний"]},
                         {"значение записанной группы", "правило для произведений"})
        self.assertEqual(s["ошибки разметки"], {"ОШИБКА: противоречивый запрет": 1})
        self.assertEqual(sorted(map(tuple, kn["корни"]["все неизвестные"])),
                         [("a(G)", "×", 2), ("c(G)", "g0", 1), ("c(G)", "g1", 1)])
        self.assertTrue(K.text(s)[0].startswith("== знания:"))


class ReviewCasesTest(unittest.TestCase):
    """Случаи из ревью 16.11: счёт по запретам, полные образы, много переменных, повторы."""

    def test_contrapositives_count_once(self):
        form = var_form([(True, None, None, None), (None, True, False, None)], ["g0", "g1"])
        # одна и та же пара литералов в двух строках (контрапозиции, один №) и ещё одна строка C
        report = [{"вердикт": "неизвестно", "_cols": [0, 5], "№": 7, "запрет": ["a(G)", "¬c(G)"]},
                  {"вердикт": "неизвестно", "_cols": [5, 0], "№": 7, "запрет": ["a(G)", "¬c(G)"]},
                  {"вердикт": "неизвестно", "_cols": [4, 1], "№": 8, "запрет": ["c(G)", "¬a(G)"]},
                  {"вердикт": "неизвестно", "_cols": [1, 4], "№": 8, "запрет": ["c(G)", "¬a(G)"]}]
        s = K.annotate(form, report)["сводка"]
        k = s["оставленные после сжатия"]
        self.assertEqual((k["строк"], k["запретов"], k["вопросов человеку (C)"], k["ждут знаний (A + B)"]), (4, 2, 1, 1))
        self.assertEqual([q["№"] for q in s["вопросы человеку"]], [8])
        self.assertEqual(s["очередь знаний"][0]["запретов"], 1)  # корень одного запрета, не двух строк
        self.assertEqual(report[0]["корни"], report[1]["корни"])

    def test_non_group_images_keep_full_identity(self):
        G = Var("G")
        f = fake([(None, True), (None, True), (None, True)], [("p", "a", G), ("p", "b", G)])
        f.lib = SimpleNamespace(obj={"6:1": {}, "×p": {"синтез": True}})
        images = [("elt", "6:1", 1), ("elt", "6:1", 2), ("elt", "×p", 5)]
        f._image = lambda r, t: images[r]
        kn = K.Knowledge(f)
        kind, n1, _n2, _n0, ids = kn.classify([0, 2])
        objs = sorted(kn.root_name(x)[1] for x in ids)
        self.assertEqual((kind, n1), ("A", 3))
        self.assertEqual(objs, sorted([repr(images[0]), repr(images[1]), "×"]))

    def test_many_variables_and_objects_do_not_overflow(self):
        vs = [Var(x) for x in "ABCD"]
        nrows, natoms = 4000, 400
        f = fake([[None] * natoms for _ in range(nrows)],
                 [("r", "rel", vs[i % 4], vs[(i + 1) % 4]) if i % 2 else ("p", f"p{i}", vs[i % 4])
                  for i in range(natoms)])
        f._image = lambda r, t: None  # «#r»: у каждой строки и переменной свой объект
        kn = K.Knowledge(f)
        kind, _n1, n2, _n0, ids = kn.classify([2 * (natoms - 1), 2 * (natoms - 3)])
        self.assertEqual((kind, n2), ("B", nrows))
        self.assertTrue(len(ids) and int(ids.max()) < 2 ** 62)
        atoms = {kn.root_name(x)[0] for x in ids}
        self.assertEqual(atoms, {kn.pattern[natoms - 1], kn.pattern[natoms - 3]})
        self.assertIn("#0, #0", {kn.root_name(x)[1] for x in ids})

    def test_hitting_ignores_repeats_inside_a_set(self):
        self.assertEqual(K.hitting([[1, 1], [2]]), 2)


class EndToEndTest(unittest.TestCase):
    """Настоящий перебор маленькой схемы: без флага выдача прежняя, флаг только добавляет поля."""

    @classmethod
    def setUpClass(cls):
        from algen.library import Library
        from algen.logic import Vocab
        cls.v = Vocab.section("grp")
        cls.lib = Library()

    def run_once(self, flag, compress=False):
        with patch.dict("os.environ", ALGEN_EAGER_SEARCH="1"):
            f = E.SchemeForm(self.lib, self.v, "∀ G : Grp", ("center(G)",), with_rows=False)
        self.addCleanup(f.sc.s.delete)
        self.addCleanup(f.search.s.delete)
        f.search.objects = ["1:1", "2:1", "6:1", "8:3", "Z", "Q", "Dinf", "F2", "BS23"]
        f.fill_rows()
        env = {"ALGEN_COMPRESS": "1"} if compress else {}
        with patch.object(E, "KNOWLEDGE", flag), patch.dict("os.environ", env):
            if not compress:
                import os
                os.environ.pop("ALGEN_COMPRESS", None)
            _, alive, empty, report = E.run(1, self.lib, self.v, f)
            summary = E.render(f, alive, empty, report, out=io.StringIO(), err=io.StringIO())
        f.mem = None  # этап «знания» в «память по этапам» — только с флагом
        return f, report, summary

    def check(self, compress):
        _, report0, summary0 = self.run_once(False, compress)
        f, report1, summary1 = self.run_once(True, compress)
        unknown = [r for r in report1 if r["вердикт"] == "неизвестно"]
        self.assertTrue(unknown, "в схеме нет неизвестных — тест ничего не проверяет")
        self.assertTrue(all(r["вид"] in ("A", "B", "C") for r in unknown))
        self.assertFalse(any("вид" in r for r in report0))
        self.assertIn("знания", summary1)
        self.assertNotIn("знания", summary0)
        kept = summary1["знания"]["оставленные после сжатия"]
        kept_rows = [r for r in unknown if not r.get("свёрнута")]
        self.assertEqual(kept["строк"], len(kept_rows))
        units = {("№", r["№"]) if "№" in r else tuple(r["класс"]) for r in kept_rows}
        self.assertEqual(kept["запретов"], len(units))
        if compress:  # оставленные запреты — те же, что «оставленные вопросы» сжатия
            self.assertEqual(kept["запретов"], len(summary1["оставленные вопросы"]))
        stripped = [{k: v for k, v in r.items() if k not in ("вид", "строк", "корней", "корни")} for r in report1]
        self.assertEqual(json.dumps(stripped, ensure_ascii=False, sort_keys=True),
                         json.dumps(report0, ensure_ascii=False, sort_keys=True))
        self.assertEqual(json.dumps({k: v for k, v in summary1.items() if k != "знания"}, ensure_ascii=False,
                                    sort_keys=True), json.dumps(summary0, ensure_ascii=False, sort_keys=True))

    def test_flag_only_adds_fields(self):
        self.check(False)

    def test_flag_only_adds_fields_with_compression(self):
        self.check(True)


if __name__ == "__main__":
    unittest.main()
