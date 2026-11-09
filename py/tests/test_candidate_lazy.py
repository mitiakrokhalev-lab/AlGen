"""Lazy proof cuts must survive or reopen correctly after row updates."""

from copy import deepcopy
import json
import unittest
from unittest.mock import patch

from tools import check_candidate_search as R
from tools.check_candidate_lazy import LazySearch, canonical, verify_generation, verify_transition


class LazyCandidateTest(unittest.TestCase):
    def check(self,d,cnf,variables,rows):
        with LazySearch(d,cnf,variables) as search:
            for i,row in enumerate(rows):
                search.add_row(str(i),row)
            result = search.search()
        models = R.truth_models(cnf,d.n,d.fixed)
        return result,verify_generation(d,variables,models,result)

    def test_seeded_whole_domains_and_every_cut(self):
        for seed in range(8100,8104):
            kw,cnf,rows,_ = R.synthetic(seed)
            for k in range(4):
                with self.subTest(seed=seed,k=k):
                    _,v = self.check(R.Domain(k=k,**kw),cnf,list(range(1,6)),rows)
                    self.assertEqual(v['uncovered'],0)

    def test_original_positive_disables_basis_and_saves_exception(self):
        with LazySearch(R.Domain(n=2,k=0),[],[1,2]) as search:
            search.add_row('unknown',(None,None))
            self.assertTrue(search._consider(((),1))['admitted'])
            self.assertFalse(search._consider(((),-1))['admitted'])
            self.assertIn(((),-1),search.outside)
            result = search.search()
            stats = verify_generation(search.d,[1,2],R.truth_models([],2),result)
            self.assertEqual(stats['unknown'],4)

    def test_refuted_basis_disables_dependent_cut_and_reopens_stronger(self):
        d = R.Domain(n=3,k=2)
        with LazySearch(d,[],[1,2,3]) as search:
            search.add_row('unknown',(None,None,None))
            search._consider(((),1))
            search._consider(((),3))
            self.assertIsNone(search._consider(((2,),1)))
            cut = search.cuts[-1]
            self.assertEqual(cut['dependencies'],(((),1),))
            # An unrelated hypothesis is refuted; this proof remains valid.
            search.add_row('not-c',(None,None,False))
            first = search.search()
            verify_generation(d,[1,2,3],R.truth_models([],3),first)
            self.assertTrue(search._cut_active(cut))
            # a is now false, but b=>a has no known-true premise in that row.
            search.add_row('not-a',(False,None,None))
            second = search.search()
            v = verify_generation(d,[1,2,3],R.truth_models([],3),second)
            self.assertFalse(search._cut_active(cut))
            self.assertIn(((),1),[canonical(q) for q in second['removed_basis']])
            self.assertEqual(R.classify(((2,),1),[(False,None,None),(None,None,False)],R.truth_models([],3)),'unknown')
            self.assertGreater(v['disabled_cuts'],0)

    def test_withdraw_row_restores_previously_refuted_candidate(self):
        d = R.Domain(n=2,k=1)
        with LazySearch(d,[],[1,2]) as search:
            search.add_row('a',(True,None))
            before = search.search()
            a = verify_generation(d,[1,2],R.truth_models([],2),before)
            self.assertEqual(R.classify(((),-1),[(True,None)],R.truth_models([],2)),'library_refuted')
            search.set_row_active('a',False)
            after = search.search()
            b = verify_generation(d,[1,2],R.truth_models([],2),after)
            verify_transition(d,R.truth_models([],2),before,after)
            self.assertGreater(b['unknown'],a['unknown'])
            self.assertEqual(R.classify(((),-1),[],R.truth_models([],2)),'unknown')
            search.set_row_active('a',True)
            verify_generation(d,[1,2],R.truth_models([],2),search.search())

    def test_old_exception_can_become_compatible_without_being_lost(self):
        d = R.Domain(n=2,k=0)
        with LazySearch(d,[],[1,2]) as search:
            search._consider(((),1))
            search._consider(((),-1))
            search.add_row('not-a',(False,None))
            search._refresh()
            self.assertNotIn(((),1),search.basis)
            self.assertIn(((),-1),search.outside)
            self.assertTrue(search._solve('validation_solves',search._theory_assumptions(search.basis)+[-1]))
            result = search.search()
            verify_generation(d,[1,2],R.truth_models([],2),result)

    def test_oracle_rejects_missing_dependency_even_when_other_rows_hide_it(self):
        d = R.Domain(n=2,k=1)
        with LazySearch(d,[],[1,2]) as search:
            search._consider(((),1))
            search._consider(((2,),1))
            result = search.search()
        broken = deepcopy(result)
        conditional = next(c for c in broken['cuts'] if c['dependencies'])
        conditional['dependencies'] = []
        with self.assertRaises(AssertionError):
            verify_generation(d,[1,2],R.truth_models([],2),broken)

    def test_json_roundtrip_and_free_hidden_variables(self):
        d = R.Domain(n=3,k=2)
        cnf,variables = [[-1,5],[-5,2]],[1,2,9]
        models = R.projected_models(cnf,variables)
        with LazySearch(d,cnf,variables) as search:
            search.add_row('partial',(True,True,None))
            result = search.search()
        self.assertEqual(verify_generation(d,variables,models,result),
                         verify_generation(d,variables,models,json.loads(json.dumps(result))))

    def test_rejects_bad_context_unproved_availability_and_bad_rows(self):
        with self.assertRaises(ValueError):
            LazySearch(R.Domain(n=2,k=1,fixed=(1,-1)),[],[1,2])
        with self.assertRaises(ValueError):
            LazySearch(R.Domain(n=2,k=1,available=(1,)),[],[1,2])
        with LazySearch(R.Domain(n=2,k=1),[[1]],[1,2]) as search:
            with self.assertRaises(ValueError):
                search.add_row('bad',(False,None))
            with self.assertRaises(ValueError):
                search.add_row('not-bool',(1,None))
            search.add_row('good',(True,None))
            with self.assertRaises(ValueError):
                search.add_row('good',(None,None))
            search.d.k = 2
            with self.assertRaises(ValueError):
                search.search()

    def test_empty_domain_and_k_larger_than_atom_count(self):
        self.check(R.Domain(n=1,k=3),[],[1],[(None,)])
        self.assertEqual(self.check(R.Domain(n=2,k=3,cover=((),)),[],[1,2],[])[1]['candidates'],0)

    def test_incomplete_solver_never_marks_current_generation_complete(self):
        with LazySearch(R.Domain(n=2,k=1),[],[1,2]) as search:
            search.search()
            search.add_row('new',(True,None))
            with patch.object(search.meta,'solve',return_value=None):
                with self.assertRaises(RuntimeError):
                    search.search()
            self.assertIsNone(search.complete_revision)
            result = search.search()
            self.assertEqual(result['revision'],search.revision)
            verify_generation(search.d,[1,2],R.truth_models([],2),result)

    def test_interrupted_cut_is_never_aliased_after_basis_refutation(self):
        d = R.Domain(n=3,k=2)
        with LazySearch(d,[],[1,2,3]) as search:
            search._consider(((),1))
            original = search.meta.add_clause
            def interrupted(c,*args,**kw):
                original(c,*args,**kw)
                raise InterruptedError('clause added, metadata not recorded')
            with patch.object(search.meta,'add_clause',side_effect=interrupted):
                with self.assertRaises(InterruptedError):
                    search._consider(((2,),1))
            self.assertFalse(search.cuts)
            search.add_row('not-a',(False,None,None))
            result = search.search()
            verify_generation(d,[1,2,3],R.truth_models([],3),result)

    def test_row_interruption_invalidates_stamp_before_both_mutations(self):
        class SavedThenInterrupted(dict):
            def __setitem__(self,key,value):
                super().__setitem__(key,value)
                raise InterruptedError('mutation completed before interruption')
        d = R.Domain(n=2,k=1)
        with LazySearch(d,[],[1,2]) as search:
            search.search()
            old_revision = search.revision
            search.rows = SavedThenInterrupted(search.rows)
            with self.assertRaises(InterruptedError):
                search.add_row('a',(True,None))
            self.assertIsNone(search.complete_revision)
            self.assertGreater(search.revision,old_revision)
            search.rows = dict(search.rows)
            before = search.search()
            search.rows['a'] = SavedThenInterrupted(search.rows['a'])
            old_revision = search.revision
            with self.assertRaises(InterruptedError):
                search.set_row_active('a',False)
            self.assertIsNone(search.complete_revision)
            self.assertGreater(search.revision,old_revision)
            search.rows['a'] = dict(search.rows['a'])
            after = search.search()
            verify_generation(d,[1,2],R.truth_models([],2),after)
            verify_transition(d,R.truth_models([],2),before,after)


if __name__=='__main__':
    unittest.main()
