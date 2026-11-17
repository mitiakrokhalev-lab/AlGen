"""Search не разделяет solver с формой и не создаёт его для образов/фактов."""

import copy
import io
import json
from pathlib import Path
import pickle
import tempfile
import unittest
from unittest.mock import Mock, patch

import numpy as np
from pysat.solvers import Solver

from algen import enumerate as E, table
from algen.deferred import DeferredSolver, make_search
from algen.library import Library, Search
from algen.logic import Graph, Theory, Vocab


class DeferredSolverTest(unittest.TestCase):
    def test_factory_once_and_full_solver_operations(self):
        factory = Mock(side_effect=lambda: Solver(name="g4", bootstrap_with=[[1, 2], [-1, 2]]))
        s = DeferredSolver(factory)
        self.addCleanup(s.delete)
        self.assertFalse(s.materialized)
        self.assertEqual(factory.call_count, 0)
        self.assertFalse(s.solve(assumptions=[-2]))
        self.assertEqual(s.get_core(), [-2])
        self.assertTrue(s.solve(assumptions=[1]))
        self.assertIn(2, s.get_model())
        s.add_clause([-1])
        self.assertFalse(s.solve(assumptions=[1]))
        self.assertEqual(factory.call_count, 1)
        s.delete()
        s.delete()
        with self.assertRaises(RuntimeError):
            s.solve()
        self.assertEqual(factory.call_count, 1)

    def test_delete_and_service_probes_never_open_factory(self):
        factory = Mock(side_effect=AssertionError("не должен создаваться"))
        s = DeferredSolver(factory)
        self.assertFalse(hasattr(s, "__setstate__"))
        self.assertFalse(hasattr(s, "__deepcopy__"))
        for operation in (pickle.dumps, copy.deepcopy):
            with self.assertRaises(TypeError):
                operation(s)
        with s:
            self.assertFalse(s.materialized)
        s.delete()
        with self.assertRaises(RuntimeError):
            s.solve()
        self.assertEqual(factory.call_count, 0)

    def test_failed_factory_does_not_leave_a_partial_solver(self):
        real = Solver(name="g4", bootstrap_with=[[1]])
        factory = Mock(side_effect=[ValueError("failed"), real])
        s = DeferredSolver(factory)
        self.addCleanup(s.delete)
        with self.assertRaises(ValueError):
            s.solve()
        self.assertFalse(s.materialized)
        self.assertTrue(s.solve())
        self.assertEqual(factory.call_count, 2)

    def test_custom_search_constructor_gets_original_theory_and_can_return_none(self):
        graph, theory, lib = object(), object(), object()
        constructor = Mock(return_value=None)
        with patch.dict("os.environ", ALGEN_EAGER_SEARCH="0"):
            self.assertIsNone(make_search(graph, theory, lib, constructor=constructor, max_order=2))
        constructor.assert_called_once_with(graph, theory, lib, max_order=2)


class SearchTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.v = Vocab.section("grp")
        cls.lib = Library()

    def form(self, eager, decl="∀ G : Grp", terms=("center(G)",)):
        with patch.dict("os.environ", ALGEN_EAGER_SEARCH="1" if eager else "0"):
            form = E.SchemeForm(self.lib, self.v, decl, terms, with_rows=False)
        self.addCleanup(form.sc.s.delete)
        self.addCleanup(form.search.s.delete)
        form.search.objects = ["1:1", "2:1", "6:1"]
        return form

    def test_images_facts_and_rows_keep_original_theory_without_solver(self):
        eager, deferred = self.form(True), self.form(False)
        self.assertIsInstance(deferred.search, Search)
        self.assertIs(deferred.search.T, deferred.sc.T)
        self.assertIs(deferred.search.g, deferred.g)
        self.assertIs(deferred.search.lib, self.lib)
        for form in (eager, deferred):
            form.fill_rows()
        self.assertEqual(eager.envs, deferred.envs)
        for name in "mse":
            np.testing.assert_array_equal(getattr(eager, name), getattr(deferred, name))
        for r in range(len(eager.envs)):
            self.assertEqual(eager.row_facts(r), deferred.row_facts(r))
            self.assertEqual(eager.where(r), deferred.where(r))
            for t in eager.own:
                self.assertEqual(eager.search._image(t, eager.envs[r]), deferred.search._image(t, deferred.envs[r]))
        self.assertFalse(deferred.search.s.materialized)
        graph = Graph(self.v)
        graph.var("A", "Grp.obj")
        graph.var("B", "Grp.obj")
        theory = Theory(graph)
        with patch.dict("os.environ", ALGEN_EAGER_SEARCH="0"):
            small = make_search(graph, theory, self.lib, max_order=2)
        direct = Search(graph, theory, self.lib, max_order=2)
        self.addCleanup(small.s.delete)
        self.addCleanup(direct.s.delete)
        self.assertEqual(small.objects, direct.objects)
        self.assertEqual(small.vars, direct.vars)
        self.assertFalse(small.s.materialized)

    def test_search_still_finds_real_witness_after_main_solver_deleted(self):
        results = []
        for eager in (True, False):
            f = self.form(eager, terms=())
            G = f.search.vars[0]
            f.sc.s.delete()
            result = f.search.witnesses([(("p", "finite", G), True)], (("p", "abelian", G), True), limit=1)
            self.assertTrue(result)
            results.append(result)
            if not eager:
                self.assertTrue(f.search.s.materialized)
        self.assertEqual(results[0], results[1])

    def test_exact_reports_cores_and_order_match_in_real_enumeration(self):
        outcomes = []
        for eager in (True, False):
            f = self.form(eager)
            f.fill_rows()
            _, alive, empty, report = E.run(1, self.lib, self.v, f)
            summary = E.render(f, alive, empty, report, out=io.StringIO(), err=io.StringIO())
            outcomes.append((list(alive.items()), empty, json.dumps(report, ensure_ascii=False, sort_keys=True), summary))
            if not eager:
                self.assertFalse(f.search.s.materialized)
        self.assertEqual(outcomes[0], outcomes[1])

    def test_cached_skeleton_roundtrip_keeps_format_and_uses_same_search_factory(self):
        f = self.form(True)
        f.sc.s.delete()
        f.search.s.delete()
        f.sc.s, f.search, f.lib = None, None, None
        with tempfile.TemporaryDirectory() as directory:
            with open(Path(directory)/"G.skel.pickle", "wb") as out:
                pickle.dump({"отпечаток": "test", "каркас": f}, out)
            with patch.object(table, "SKEL_DIR", directory), patch.object(table, "SIZE", 0), \
                    patch.object(table, "_fp", return_value="test"), patch.dict("os.environ", ALGEN_EAGER_SEARCH="0"):
                loaded = table.skeleton(self.lib, self.v, "G")
            self.addCleanup(loaded.sc.s.delete)
            self.addCleanup(loaded.search.s.delete)
            self.assertIs(loaded.search.T, loaded.sc.T)
            self.assertIs(loaded.lib, self.lib)
            self.assertIsInstance(loaded.search.s, DeferredSolver)
            self.assertFalse(loaded.search.s.materialized)
            loaded.search.objects = ["1:1", "2:1"]
            loaded.fill_rows()
            self.assertFalse(loaded.search.s.materialized)
        with tempfile.TemporaryDirectory() as directory:
            with patch.object(table, "SKEL_DIR", directory), patch.object(table, "SIZE", 0), \
                    patch.object(table, "_fp", return_value="test"), \
                    patch.object(table, "universe", return_value=["center(G)"]), \
                    patch.dict("os.environ", ALGEN_EAGER_SEARCH="0"):
                built = table.skeleton(self.lib, self.v, "G")
            self.addCleanup(built.sc.s.delete)
            self.addCleanup(built.search.s.delete)
            self.assertFalse(built.search.s.materialized)
            self.assertIs(built.search.T, built.sc.T)
            with open(Path(directory)/"G.skel.pickle", "rb") as saved:
                data = pickle.load(saved)
            self.assertIsNone(data["каркас"].search)
            self.assertIsNone(data["каркас"].sc.s)
            self.assertEqual(data["отпечаток"], "test")


if __name__ == "__main__":
    unittest.main()
