"""Different proof views share an immutable CNF, never permanent row facts."""
from pathlib import Path
from copy import copy
import sys
import tempfile
import unittest
from unittest.mock import patch

from algen.frozen_theory import FrozenTheoryBasis
from algen.row_knowledge import FrozenRowTheory, RowKnowledge
from algen.value_ledger import ValueLedger
from test_row_knowledge import source, theory_for
from test_value_classify import fake, packed
from test_value_ledger import MANIFEST, SOURCE


class FrozenTheoryTest(unittest.TestCase):
    def fixture(self):
        full = fake([(True,None,None)])
        return full,theory_for(full,[[-1,2],[-2,3]])

    def test_distinct_views_opposite_facts_and_certificates_are_isolated(self):
        f,t = self.fixture()
        with FrozenTheoryBasis(t,'two distinct views') as basis:
            with FrozenRowTheory(t,f.atoms[:2],'two distinct views',basis=basis) as a, \
                 FrozenRowTheory(t,f.atoms[1:],'two distinct views',basis=basis) as b:
                yes = a.derive(1,{1})
                no = b.derive(0,{-3})
                self.assertTrue(yes['value'])
                self.assertFalse(no['value'])
                self.assertEqual([p['literal'] for p in yes['core']],[1])
                self.assertEqual([p['literal'] for p in no['core']],[-3])
                self.assertIs(a._solver,b._solver)
                self.assertNotEqual(a.identity,b.identity)
                self.assertIsNone(a.derive(1,set()))
                with self.assertRaisesRegex(ValueError,'context'):b.verify(yes)
                self.assertEqual(basis.stats()['solver_bootstraps'],1)
                self.assertEqual(basis.stats()['views_bound'],2)
                for obj in (a,b,basis):
                    self.assertFalse(hasattr(obj,'solver'))
                    self.assertFalse(hasattr(obj,'stable'))

    def test_default_private_views_and_shared_views_keep_v1_protocol(self):
        f,t = self.fixture()
        with FrozenRowTheory(t,f.atoms,'protocol-compatibility-v1') as own, \
             FrozenTheoryBasis(t,'protocol-compatibility-v1') as basis, \
             FrozenRowTheory(t,f.atoms,'protocol-compatibility-v1',basis=basis) as shared:
            # Captured from the independently verified PR22 implementation,
            # before this refactor, on its native little-endian array layout.
            if sys.byteorder == 'little':
                self.assertEqual(own.identity,'3cc8bf74118d5e4f11b7cbe36a53b4aa40d5b256abd34bd9c630f60c47a31a7c')
            self.assertEqual(own.header,shared.header)
            self.assertEqual(own.identity,shared.identity)
            self.assertEqual(own.derive(1,{1}),shared.derive(1,{1}))
            self.assertIsNot(own._solver,shared._solver)

    def test_borrowed_view_lifetime_owner_and_reference(self):
        f,t = self.fixture()
        other = theory_for(f,[[-1,2],[-2,3]])
        basis = FrozenTheoryBasis(t,dict(version='frozen-input'))
        try:
            with self.assertRaisesRegex(ValueError,'owner and reference'):
                FrozenRowTheory(other,f.atoms,dict(version='frozen-input'),basis=basis)
            with self.assertRaisesRegex(ValueError,'owner and reference'):
                FrozenRowTheory(t,f.atoms,dict(version='different-input'),basis=basis)
            a = FrozenRowTheory(t,f.atoms[:2],dict(version='frozen-input'),basis=basis)
            a.derive(1,{1});a.close()
            with FrozenRowTheory(t,f.atoms[1:],dict(version='frozen-input'),basis=basis) as b:
                self.assertFalse(b.derive(0,{-3})['value'])
                self.assertEqual(basis.stats()['solver_bootstraps'],1)
                with a._basis._stable():
                    with self.assertRaisesRegex(RuntimeError,'cannot close'):b.close()
                    with self.assertRaisesRegex(RuntimeError,'cannot close'):basis.close()
                basis.close()
                with self.assertRaisesRegex(RuntimeError,'closed'):b.derive(0,{-3})
        finally:
            basis.close()

    def test_cross_view_nested_operation_and_edited_snapshot_cannot_commit(self):
        f,t = self.fixture()
        with FrozenTheoryBasis(t,'shared') as basis, \
             FrozenRowTheory(t,f.atoms[:2],'shared',basis=basis) as a, \
             FrozenRowTheory(t,f.atoms[1:],'shared',basis=basis) as b:
            with a._stable():
                with self.assertRaisesRegex(RuntimeError,'reentrant'):
                    with b._stable():pass
            a.derive(1,{1})
            with self.assertRaisesRegex(ValueError,'Theory changed'):
                with b._stable():
                    t.clauses.data[1] = -2
            self.assertIsNone(a._solver)
            t.clauses.data[1] = 2
            self.assertTrue(a.derive(1,{1})['value'])
            self.assertFalse(b.derive(0,{-3})['value'])

    def test_failed_direct_bootstrap_discards_contaminated_solver_without_transaction(self):
        from pysat.solvers import Solver
        f,t = self.fixture()
        with FrozenTheoryBasis(t,'bootstrap fault') as basis, \
             FrozenRowTheory(t,f.atoms,'bootstrap fault',basis=basis) as a:
            def changed(*args,**kwargs):
                t.clauses.data[1] = -2
                return Solver(*args,**kwargs)
            try:
                with patch('algen.frozen_theory.Solver',changed):
                    with self.assertRaisesRegex(ValueError,'Theory changed'):a.derive(1,{1})
                self.assertIsNone(a._solver)
            finally:
                t.clauses.data[1] = 2
            self.assertTrue(a.derive(1,{1})['value'])
            self.assertEqual(basis.stats()['solver_bootstrap_attempts'],2)
            self.assertEqual(basis.stats()['solver_bootstraps'],1)

    def test_stats_are_aggregates_and_do_not_modify_proof_identity(self):
        f,t = self.fixture()
        with FrozenTheoryBasis(t,'timed') as basis, FrozenRowTheory(t,f.atoms,'timed',basis=basis) as a:
            identity = a.identity
            a.derive(1,{1})
            stats = basis.stats()
            self.assertEqual(stats['snapshot_builds'],1)
            self.assertGreater(stats['clause_hash_calls'],0)
            for k,v in stats.items():
                if k.endswith('_seconds'):self.assertGreaterEqual(v,0.)
            stats['solver_bootstraps'] = 999
            self.assertEqual(basis.stats()['solver_bootstraps'],1)
            self.assertEqual(a.identity,identity)

    def test_shared_basis_aliases_preserve_each_view_structural_targets(self):
        f,t = self.fixture()
        t = theory_for(f,[[-1,2]],aliases={1:1})
        with FrozenTheoryBasis(t,'alias') as basis, \
             FrozenRowTheory(t,f.atoms[:2],'alias',basis=basis) as a, \
             FrozenRowTheory(t,f.atoms[1:],'alias',basis=basis) as b:
            ca,cb = a.derive(1,{1}),b.derive(0,{1})
            self.assertEqual(ca['target'],cb['target'])
            self.assertNotEqual(ca['context'],cb['context'])
            self.assertEqual(a.verify(ca),[1])
            self.assertEqual(b.verify(cb),[1])
            self.assertEqual(basis.stats()['solver_bootstraps'],1)

    def test_public_owner_schema_and_namespace_changes_cannot_create_new_views(self):
        f,t = self.fixture()
        with FrozenTheoryBasis(t,'frozen eligibility') as basis:
            original = t.atoms[1]
            t.atoms[1] = ('p','replacement','G')
            with self.assertRaisesRegex(ValueError,'Theory changed'):basis.check(force=True)
            t.atoms[1] = original
            late = ('p','late-new-target','G')
            t.var[late] = 1
            try:
                with self.assertRaisesRegex(ValueError,'Theory changed'):
                    FrozenRowTheory(t,[f.atoms[0],late],'frozen eligibility',basis=basis)
            finally:
                del t.var[late]
            replacement = copy(t)
            basis.theory = replacement
            with self.assertRaisesRegex(ValueError,'Theory changed'):
                FrozenRowTheory(replacement,f.atoms,'frozen eligibility',basis=basis)
            basis.theory = t
            with FrozenRowTheory(t,f.atoms,'frozen eligibility',basis=basis) as view:
                self.assertTrue(view.derive(1,{1})['value'])

    def test_typed_equal_schema_replacement_and_live_cache_rebind_are_rejected(self):
        f = fake([(True,None)],[('p','a',1),('p','b',1)])
        t = theory_for(f,[[-1,2]])
        with FrozenTheoryBasis(t,'typed') as basis:
            original = t.atoms[0]
            t.atoms[0] = ('p','a',True)
            self.assertEqual(original,t.atoms[0])
            with self.assertRaisesRegex(ValueError,'Theory changed'):basis.check(force=True)
            t.atoms[0] = original
            t._lc[original] = 2
            with self.assertRaisesRegex(ValueError,'cache rebound'):basis.check(force=True)
            t._lc[original] = 1
            with FrozenRowTheory(t,f.atoms,'typed',basis=basis) as view:
                self.assertTrue(view.derive(1,{1})['value'])

    def test_real_symmetric_alias_and_new_reflexive_cache_entries_are_allowed(self):
        from algen.logic import Var
        x,y = Var('X'),Var('Y')
        canonical_atom = ('r','iso',x,y)
        reverse,constant = ('r','iso',y,x),('r','iso',x,x)
        f = fake([(None,)],[canonical_atom])
        t = theory_for(f,[])
        with FrozenTheoryBasis(t,'real alias') as basis:
            self.assertNotIn(reverse,t._lc)
            self.assertEqual(t.lit(reverse),1)
            self.assertIsNone(t.lit(constant))
            basis.check(force=True)
            with FrozenRowTheory(t,[reverse,constant],'real alias',basis=basis) as view:
                self.assertEqual(view.literals,[1,0])
                self.assertTrue(view.derive(0,{1})['value'])
                self.assertTrue(view.derive(1,set())['value'])

    def test_two_ledgers_share_theory_but_not_source_withdrawal_or_revisions(self):
        f,t = self.fixture()
        aform = fake([(True,None)],f.atoms[:2])
        bform = fake([(None,False)],f.atoms[1:])
        aq,bq = packed(aform,[((),2)]),packed(bform,[((),0)])
        with tempfile.TemporaryDirectory(prefix='algen-two-views-') as directory, \
             FrozenTheoryBasis(t,'two ledgers') as basis, \
             FrozenRowTheory(t,aform.atoms,'two ledgers',basis=basis) as av, \
             FrozenRowTheory(t,bform.atoms,'two ledgers',basis=basis) as bv, \
             ValueLedger.create(Path(directory)/'a.sqlite',aform,aq,[dict(concrete=0)],MANIFEST,SOURCE) as ad, \
             ValueLedger.create(Path(directory)/'b.sqlite',bform,bq,[dict(concrete=0)],MANIFEST,SOURCE) as bd:
            ak,bk = RowKnowledge(ad,av,0),RowKnowledge(bd,bv,0)
            ap,bp = source('a',[(0,True)]),source('b',[(1,False)])
            ak.enroll('enroll',[ap],0);bk.enroll('enroll',[bp],0)
            ak.derive('q',1,1);bk.derive('not-q',0,1)
            self.assertEqual(ad.summary()['kinds'],{'C':1})
            self.assertEqual(bd.summary()['kinds'],{'R':1})
            ak.withdraw('withdraw','a','1',2)
            self.assertEqual(ad.summary()['kinds'],{'A':1})
            self.assertEqual(bd.summary()['kinds'],{'R':1})
            ak.put_source('restore',ap,3)
            self.assertEqual(ad.summary()['kinds'],{'C':1})
            self.assertEqual(bd.summary()['revision'],2)
            self.assertEqual(ad.summary()['proof_pending'],1)
            self.assertEqual(bd.summary()['proof_pending'],1)
            self.assertEqual(basis.stats()['solver_bootstraps'],1)


if __name__=='__main__':unittest.main()
