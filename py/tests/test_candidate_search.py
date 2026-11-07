"""Research encoding versus independent exhaustive truth-table coverage."""

from copy import deepcopy
import json
import unittest

from tools.check_candidate_search import (Domain, all_candidates, classify,
    find_basis, projected_models, synthetic, truth_models, verify)


class CandidateSearchTest(unittest.TestCase):
    def checked(self, d, cnf=(), rows=None):
        rows = rows if rows is not None else [(None,) * d.n]
        models = truth_models(cnf, d.n, d.fixed)
        result = find_basis(d, cnf, list(range(1, d.n + 1)), rows)
        return result, verify(d, rows, models, result)

    def test_zero_premises_incompatible_questions_stay_explicit(self):
        result, stats = self.checked(Domain(n=2, k=0))
        self.assertEqual(stats['candidates'], 4)
        self.assertEqual(stats['checked_unknown'], 4)
        self.assertEqual(stats['basis'], 2)
        self.assertEqual(stats['exceptions'], 2)
        self.assertEqual(stats['retained'], 4)
        self.assertEqual(result['stats']['meta_solves'], 5)
        self.assertTrue(all(not q[0] for q in result['basis']+result['exceptions']))

    def test_single_atom_and_empty_required_cover(self):
        self.assertEqual(self.checked(Domain(n=1,k=3))[1]['checked_unknown'],2)
        self.assertEqual(self.checked(Domain(n=2,k=3,cover=((),)))[1]['candidates'],0)

    def test_requirements_and_coverage_use_selectors(self):
        d = Domain(n=3, k=2, requirements={3: (1,)}, cover=((2,), (3,)))
        candidates = set(all_candidates(d))
        self.assertNotIn(((2,), 3), candidates)
        self.assertIn(((1, 2), 3), candidates)
        self.assertTrue(all(abs(goal) not in {abs(p) for p in prem} for prem, goal in candidates))
        self.checked(d)
        # Proving the requirement makes it available, without selecting it.
        d.available = (1,)
        self.assertIn(((2,), 3), set(all_candidates(d)))
        self.checked(d, cnf=[[1]])

    def test_unknown_is_not_derived_or_opposite_derived(self):
        d = Domain(n=3, k=0)
        result, stats = self.checked(d, cnf=[[1], [-2]])
        self.assertEqual(stats['checked_unknown'], 2)
        self.assertEqual(stats['kinds']['derived'], 2)
        self.assertEqual(stats['kinds']['theory_refuted'], 2)
        self.assertTrue(all(abs(q[1]) == 3 for q in result['basis']+result['exceptions']))

    def test_partial_rows_and_all_known_counterexamples(self):
        for rows in ([(True, None, False)], [(None, None, None)],
                     [(True, True, False), (False, None, True)], []):
            self.checked(Domain(n=3, k=3), rows=rows)
        self.assertEqual(classify(((1,), 2), [(True, None)], [(True, False),(True,True)]), 'unknown')
        self.assertEqual(classify(((1,), 2), [(True, False)], [(True, False),(True,True)]), 'library_refuted')

    def test_bad_context_rows_and_unproved_requirements_fail(self):
        for d, cnf, rows in (
            (Domain(n=2,k=1,fixed=(1,-1)), [], [(None,None)]),
            (Domain(n=2,k=1,available=(1,)), [], [(None,None)]),
            (Domain(n=2,k=1), [[1]], [(False,None)]),
            (Domain(n=2,k=1), [], [(0,None)]),
        ):
            with self.assertRaises(ValueError):
                find_basis(d, cnf, [1,2], rows)

    def test_independent_oracle_detects_missing_exception(self):
        d = Domain(n=2,k=0)
        rows, models = [(None,None)], truth_models([],2)
        result = find_basis(d, [], [1,2], rows)
        corrupt = deepcopy(result)
        lost = corrupt['exceptions'].pop()
        corrupt['trace'] = [r for r in corrupt['trace'] if (tuple(r['prem']),r['goal']) != lost]
        with self.assertRaises(AssertionError):
            verify(d, rows, models, corrupt)

    def test_saved_json_receipt_is_verifiable(self):
        d = Domain(n=3,k=2)
        rows, models = [(True,None,False)], truth_models([],3)
        result = find_basis(d, [], [1,2,3], rows)
        saved = json.loads(json.dumps(result))
        self.assertEqual(verify(d,rows,models,result), verify(d,rows,models,saved))

    def test_projected_oracle_keeps_hidden_variables_and_free_atoms(self):
        # x3 is hidden; eliminating it yields x1 -> x2. x4 is free.
        models = projected_models([[-1,3],[-3,2]], [1,2,4])
        expected = [m for m in truth_models([[-1,2]],3)]
        self.assertEqual(models, expected)

    def test_seeded_complete_domains_k_zero_through_three(self):
        for seed in range(8100,8104):
            kw, cnf, rows, models = synthetic(seed)
            for k in range(4):
                with self.subTest(seed=seed,k=k):
                    d = Domain(k=k, **kw)
                    result = find_basis(d, cnf, list(range(1,6)), rows)
                    self.assertEqual(verify(d,rows,models,result)['uncovered'],0)


if __name__ == '__main__':
    unittest.main()
