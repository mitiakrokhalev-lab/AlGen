"""Инкрементальные опровержения сверяются с полным просмотром строк."""

import copy
import json
from pathlib import Path
import random
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

import numpy as np

from algen import enumerate as E
from algen.live import LiveArchive, export_matches, library_row, write_report
from algen.live_bridge import append_rows, settings


def header(scheme="S", **kw):
    return dict({"base": "G", "class": "", "theory": "T", "library": "L", "declaration": "∀ G : Grp",
                 "scheme": scheme, "fixed": [], "variables": ["G"], "format": "algen.full-report", "version": 1, "complete": True}, **kw)


def question(local, forbidden, dependencies=(), **kw):
    return dict({"№": local, "класс": list(forbidden), "запрет": list(forbidden), "вердикт": "неизвестно",
                 "свёрнута": bool(dependencies), "следует из": list(dependencies)}, **kw)


def packet(name, facts, **kw):
    return dict({"key": name, "assignment": {"G": ["obj", name]}, "facts": facts,
                 "source": {"kind": "library", "reference": "проверенная запись " + name}}, **kw)


class ArchiveCase(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.path = str(Path(self.tmp.name) / "archive.sqlite")
        self.a = LiveArchive(self.path)

    def tearDown(self):
        self.a.close()
        self.tmp.cleanup()

    def state(self, ctx):
        return {alias: r["archive_state"] for r in self.a.questions(ctx) for alias in r["aliases"]}


class LiveTest(ArchiveCase):

    def test_incremental_merge_unknown_and_no_mixing_assignments(self):
        ctx = self.a.import_report(header(), [question("a", ["p(G)", "¬q(G)"])])
        self.a.apply_example(ctx, packet("x", {"p(G)": True}))
        self.a.apply_example(ctx, packet("y", {"q(G)": False}))
        self.assertEqual(self.state(ctx), {"a": "open"})
        self.a.apply_example(ctx, packet("x", {"q(G)": False}))
        self.assertEqual(self.state(ctx), {"a": "refuted"})
        evidence = list(self.a.questions(ctx))[0]["counterexamples"]
        self.assertEqual(evidence[0]["key"], "x")
        self.assertEqual(evidence[0]["forbidden"], ["p(G)", "¬q(G)"])
        self.assertEqual(len(evidence[0]["source_history"]), 2)
        before = self.a.stats(ctx)["revision"]
        self.a.apply_example(ctx, packet("x", {"q(G)": False}))
        self.assertEqual(self.a.stats(ctx)["revision"], before)
        self.a.apply_example(ctx, packet("x", {"q(G)": None}))
        self.assertEqual(self.state(ctx), {"a": "open"})
        self.assertEqual({j["kind"] for j in self.a.stats(ctx)["pending"]}, {"enumerate", "compress"})

    def test_reopen_transitively_even_if_child_not_refuted(self):
        rows = [question("a", ["p", "¬q"]), question("b", ["p", "c", "¬q"], ["a"]),
                question("c", ["p", "c", "d", "¬q"], ["b"])]
        ctx = self.a.import_report(header(), rows)
        self.assertEqual(self.state(ctx), {"a": "open", "b": "folded", "c": "folded"})
        self.a.apply_example(ctx, packet("x", {"p": True, "q": False}))
        self.assertEqual(self.state(ctx), {"a": "refuted", "b": "open", "c": "open"})
        self.a.withdraw(ctx, "x", {"kind": "user", "reference": "исправление данных"})
        self.assertEqual(self.state(ctx), {"a": "open", "b": "open", "c": "open"})
        self.assertEqual(list(self.a.records(ctx, "S")), rows)

    def test_multiple_witnesses_withdrawal_and_history_survive_reopen(self):
        ctx = self.a.import_report(header(), [question("a", ["p", "¬q"])])
        for key in ("x", "y"):
            self.a.apply_example(ctx, packet(key, {"p": True, "q": False}))
        self.a.withdraw(ctx, "x", {"kind": "user", "reference": "отзыв x"})
        self.assertEqual(self.state(ctx)["a"], "refuted")
        self.a.withdraw(ctx, "y", {"kind": "user", "reference": "отзыв y"})
        self.assertEqual(self.state(ctx)["a"], "open")
        self.a.close()
        self.a = LiveArchive(self.path)
        self.assertEqual(self.state(ctx)["a"], "open")
        self.assertEqual(self.a.db.execute("SELECT count(*) FROM examples").fetchone()[0], 4)

    def test_fixed_class_is_required_and_isolates_context(self):
        ctx = self.a.import_report(header(fixed=["finite(G)"]), [question("a", ["p", "¬q"])])
        other = self.a.import_report(header("Other"), [question("a", ["p", "¬q"])])
        self.assertNotEqual(ctx, other)
        self.a.apply_example(ctx, packet("x", {"p": True, "q": False}))
        self.assertEqual(self.state(ctx)["a"], "open")
        self.a.apply_example(ctx, packet("x", {"finite(G)": True}))
        self.assertEqual(self.state(ctx)["a"], "refuted")
        self.assertEqual(self.state(other)["a"], "open")

    def test_all_symmetric_variants_are_indexed(self):
        rows = [question("a", ["p(A)", "¬q(B)"], **{"класс": ["canonical"]}),
                question("a", ["p(B)", "¬q(A)"], **{"класс": ["canonical"]})]
        ctx = self.a.import_report(header(), rows)
        self.a.apply_example(ctx, packet("x", {"p(B)": True, "q(A)": False}))
        self.assertEqual(self.state(ctx), {"a": "refuted"})
        self.assertEqual(list(self.a.questions(ctx))[0]["counterexamples"][0]["forbidden"], ["p(B)", "¬q(A)"])
        self.assertEqual(list(self.a.records(ctx, "S")), rows)

    def test_sources_types_assignment_and_corrections(self):
        ctx = self.a.import_report(header(), [question("a", ["p", "¬q"])])
        for p in (packet("x", {"p": 1}), packet("x", {"p": True}, source={"kind": "sat", "reference": "model"})):
            with self.assertRaises(ValueError):
                self.a.apply_example(ctx, p)
        self.a.apply_example(ctx, packet("x", {"p": True, "q": True}))
        with self.assertRaises(ValueError):
            self.a.apply_example(ctx, packet("x", {"q": False}))
        with self.assertRaises(ValueError):
            self.a.apply_example(ctx, packet("x", {"p": True}, assignment={"G": ["obj", "other"]}))
        self.a.apply_example(ctx, packet("x", {"p": True, "q": False}), replace=True)
        self.assertEqual(self.state(ctx)["a"], "refuted")

    def test_proved_conflict_rolls_back_everything(self):
        ctx = self.a.import_report(header(), [question("a", ["p", "¬q"], **{"вердикт": "выводится"})])
        before = self.a.stats(ctx)
        with self.assertRaisesRegex(ValueError, "доказанному"):
            self.a.apply_example(ctx, packet("x", {"p": True, "q": False}))
        self.assertEqual(self.a.stats(ctx), before)
        self.assertEqual(self.a.db.execute("SELECT count(*) FROM examples").fetchone()[0], 0)

    def test_new_scheme_sees_old_example_and_refuted_parent(self):
        ctx = self.a.import_report(header("A"), [question("a", ["p", "¬q"])])
        self.a.apply_example(ctx, packet("x", {"p": True, "q": False}))
        same = self.a.import_report(header("B"), [question("b", ["p", "c", "¬q"], ["A:a"])])
        self.assertEqual(same, ctx)
        self.assertEqual(self.state(ctx), {"a": "refuted", "b": "open"})

    def test_unresolved_and_cross_scheme_cycles_do_not_hide_questions(self):
        ctx = self.a.import_report(header("A"), [question("a", ["p", "¬q"], ["B:b"])])
        self.assertEqual(self.state(ctx)["a"], "open")
        self.assertEqual(self.a.stats(ctx)["pending"][0]["kind"], "compress")
        with self.assertRaisesRegex(ValueError, "цикл"):
            self.a.import_report(header("B"), [question("b", ["p", "¬q"], ["A:a"])])
        self.assertEqual(self.a.stats(ctx)["schemes"], {1: 1})
        self.assertEqual(self.state(ctx), {"a": "open"})

    def test_import_does_not_discard_manual_or_error_rows(self):
        rows = [dict(question(str(i), ["p", "¬q"]), вердикт=verdict)
                for i, verdict in enumerate(("трудный контрпример", "короткий довод", "ОШИБКА: выводится, а библиотека опровергает", "противоречие"))]
        ctx = self.a.import_report(header(), rows)
        self.assertEqual(list(self.a.records(ctx, "S")), rows)

    def test_atomic_export_import_and_collision_rollback(self):
        rows = [question("a", ["p", "¬q"]), question("b", ["p", "c", "¬q"], ["a"])]
        path = Path(self.tmp.name) / "S.archive.jsonl.gz"
        write_report(path, header(), rows)
        self.assertTrue(export_matches(path, "S", "L"))
        self.assertFalse(export_matches(path, "wrong", "L"))
        self.assertFalse(export_matches(path, "S", "other-library"))
        self.assertFalse(export_matches(path.with_name("absent.gz"), "S", "L"))
        ctx = self.a.import_file(path)
        self.assertEqual(list(self.a.records(ctx, "S")), rows)
        with self.assertRaises(ValueError):
            self.a.import_report(header("bad"), [question("x", ["p"]), question("x", ["q"])])
        self.assertEqual(self.a.stats(ctx)["schemes"], {1: 1})

    def test_unconditional_facts_and_carry_to_new_snapshot(self):
        path = Path(self.tmp.name) / "S.archive.jsonl.gz"
        write_report(path, header(), [question("a", ["p", "¬q"])], ["always(G)"])
        ctx = self.a.import_file(path)
        self.assertEqual(self.a.stats(ctx)["states"], {"open": 1, "proved": 1})
        with self.assertRaisesRegex(ValueError, "доказанному"):
            self.a.apply_example(ctx, packet("bad", {"always(G)": False}))
        self.a.apply_example(ctx, packet("x", {"p": True, "q": False}))
        newer = self.a.import_report(header(library="L2"), [question("a", ["p", "¬q"])])
        self.a.carry_examples(ctx, newer)
        self.assertEqual(self.state(newer), {"a": "refuted"})
        before = self.a.stats(newer)
        self.a.carry_examples(ctx, newer)
        self.assertEqual(self.a.stats(newer), before)
        other = self.a.import_report(header(theory="different"), [])
        with self.assertRaisesRegex(ValueError, "перепроверки"):
            self.a.carry_examples(ctx, other)

    def test_incremental_answers_match_full_brute_force_after_updates(self):
        rng = random.Random(28)
        atoms = ["p", "q", "r", "s", "t"]
        rows = [question(str(i), [("¬" if rng.randrange(2) else "") + a for a in rng.sample(atoms, rng.randint(1, 4))])
                for i in range(35)]
        ctx = self.a.import_report(header(), rows)
        known = {}
        for step in range(60):
            name = "object-" + str(rng.randrange(7))
            facts = {a: bool(rng.randrange(2)) for a in rng.sample(atoms, rng.randrange(6))}
            known[name] = facts
            self.a.apply_example(ctx, packet(name, facts), replace=True)
            got = self.state(ctx)
            for q in rows:
                refuted = any(all(a.lstrip("¬") in f and f[a.lstrip("¬")] == (not a.startswith("¬")) for a in q["запрет"])
                              for f in known.values())
                self.assertEqual(got[q["№"]] == "refuted", refuted, (step, q))


class BridgeTest(ArchiveCase):
    # Только собственные bridge-проверки; основной набор у LiveTest.
    def make_form(self):
        from algen.logic import Graph, Theory, Vocab
        v = Vocab({"id": "grp", "subsorts": [], "properties": [{"id": p, "sort": "Grp.obj"} for p in ("p", "q")],
                   "relations": [], "constructions": [], "degenerations": [], "rules": []})
        g = Graph(v)
        G = g.var("G", "Grp.obj")
        atoms = [("p", p, G) for p in ("p", "q")]
        T = Theory(g, grow=0, extra=atoms)
        f = E.SchemeForm.__new__(E.SchemeForm)
        f.g, f.own, f.atoms, f.index = g, [G], atoms, {a: i for i, a in enumerate(atoms)}
        f.fixed_lits, f.fixed, f.req = [], [], {}
        f.m = f.s = f.e = np.array([[1, 0, 1, 0]], dtype=bool)
        f.envs, f._facts, f._derived, f._kept = [{G: ("obj", "old")}], {}, {}, {}
        f.sc = SimpleNamespace(T=T, s=T.solver())
        f.search = SimpleNamespace(vars=[G], _image=lambda t, env: env.get(t), _name=lambda im: im[1])
        f.lib = SimpleNamespace(obj={"old": {"синтез": False}})
        return f

    def test_overlay_changes_minimality_exactly_like_full_new_matrix(self):
        ctx = self.a.import_report(header(), [question("a", ["p(G)", "¬q(G)"])])
        self.a.apply_example(ctx, packet("new", {"p(G)": True, "q(G)": False}))
        with patch.dict("os.environ", {"ALGEN_DYNAMIC_DB": self.path, "ALGEN_DYNAMIC_CONTEXT": ctx}):
            config = settings()
        f = self.make_form()
        try:
            before, _ = E.enumerate_form(f, 1)
            self.assertIn(((0,), 2), before)
            append_rows(f, config, "G", "", "T")
            after, _ = E.enumerate_form(f, 1)
            self.assertNotIn(((0,), 2), after)
            self.assertIn(((3,), 0), after)
            self.assertIn("new", f.where(1))
            self.assertFalse(f.synthetic(1))
            self.assertIsNone(f._image(1, f.own[0]))
            self.assertTrue(f.row_facts(1)[0])
            np.testing.assert_array_equal(f.row_keeping(1, frozenset(), "трудно"), f.m[1])
            expected = self.make_form()
            expected.m = expected.s = expected.e = np.array([[1, 0, 1, 0], [1, 0, 0, 1]], dtype=bool)
            try:
                fresh, _ = E.enumerate_form(expected, 1)
                self.assertEqual(list(after.items()), list(fresh.items()))
            finally:
                expected.sc.s.delete()
        finally:
            f.sc.s.delete()

    def test_library_packet_normalizes_assignment_and_settings_revisions(self):
        ctx = self.a.import_report(header(), [question("a", ["p(G)", "¬q(G)"])])
        f = self.make_form()
        try:
            p = library_row(f, 0, "готовая Library")
            self.a.apply_example(ctx, p)
            self.a.apply_example(ctx, p)
            self.assertEqual(self.a.stats(ctx)["revision"], 1)
            with patch.dict("os.environ", {"ALGEN_DYNAMIC_DB": self.path, "ALGEN_DYNAMIC_CONTEXT": ctx}):
                config = settings()
                self.a.apply_example(ctx, packet("x", {}))
                with self.assertRaisesRegex(ValueError, "перепланировать"):
                    append_rows(f, config, "G", "", "T")
        finally:
            f.sc.s.delete()

    def test_new_minimal_superset_requires_full_enumeration(self):
        from test_enumerate import FakeForm
        old = FakeForm([(True, True, True), (False, False, True)])
        a, _ = E.enumerate_form(old, 2)
        self.assertIn(((0,), 2), a)  # p ⇒ q
        self.assertNotIn(((0, 4), 2), E.minimal(a))
        new = FakeForm([(True, True, True), (False, False, True), (True, False, False)])
        b, _ = E.enumerate_form(new, 2)
        self.assertNotIn(((0,), 2), b)
        self.assertIn(((0, 4), 2), E.minimal(b))  # теперь минимально p ∧ r ⇒ q

    def test_different_databases_same_revision_have_different_fingerprint(self):
        ctx = self.a.import_report(header(), [question("a", ["p(G)", "¬q(G)"])])
        self.a.apply_example(ctx, packet("x", {"p(G)": True}))
        other_path = str(Path(self.tmp.name) / "other.sqlite")
        with LiveArchive(other_path) as other:
            self.assertEqual(other.import_report(header(), [question("a", ["p(G)", "¬q(G)"])]), ctx)
            other.apply_example(ctx, packet("x", {"p(G)": False}))
        values = []
        for path in (self.path, other_path):
            with patch.dict("os.environ", {"ALGEN_DYNAMIC_DB": path, "ALGEN_DYNAMIC_CONTEXT": ctx}):
                values.append(settings())
        self.assertEqual(values[0]["revision"], values[1]["revision"])
        self.assertNotEqual(values[0]["fingerprint"], values[1]["fingerprint"])

    def test_table_export_does_not_enable_unrequested_verdict_cache(self):
        from algen import table
        form = SimpleNamespace(fixed_lits=[], search=SimpleNamespace(vars=["G"]), skipped=[])
        observed = []

        def run(*args):
            observed.append(E.VCACHE_OUT)
            return form, {}, [], [question("a", ["p(G)", "¬q(G)"])]

        with patch.dict("os.environ", {"ALGEN_DYNAMIC_EXPORT": "1"}), \
                patch.dict(table._STATE, {"forms": {"G": form}, "lib": None, "vocab": None, "registry": {}}, clear=True), \
                patch.object(table, "STATE_IN", ""), patch.object(table, "STATE_SAVE", False), \
                patch.object(table, "_rss_gb", return_value=0), \
                patch.object(table, "LOCAL_PRECHECK", False), patch.object(table, "view", return_value=form), \
                patch.object(table, "theory_print", return_value="T"), patch.object(E, "run", side_effect=run), \
                patch.object(E, "render", return_value={"факты без посылок": ["q(G)"]}):
            table._one(("G", "S", [], 1, self.tmp.name, "L"))
        self.assertEqual(observed, [None])
        status = json.loads((Path(self.tmp.name) / "S.json").read_text())
        self.assertEqual(status["статус"], "ok")
        self.assertNotIn("кэш вердиктов", status)
        ctx = self.a.import_file(Path(self.tmp.name) / "S.archive.jsonl.gz")
        self.assertEqual(len(list(self.a.records(ctx, "S"))), 2)
