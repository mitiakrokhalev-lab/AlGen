"""Checked Boolean entailments, not claims about new mathematical groups."""
from copy import deepcopy
from array import array
import hashlib
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import numpy as np

from algen.logic import Theory, ClauseStore, Var
from algen.row_knowledge import FrozenRowTheory, RowKnowledge
from algen.value_ledger import ValueLedger, canonical
from test_value_classify import fake, packed
from test_value_ledger import MANIFEST, SOURCE


def theory_for(form, clauses=(), aliases=None):
    t = object.__new__(Theory)
    aliases = aliases or {}
    t.atoms, t.var, t._lc = [], {}, {}
    for i, a in enumerate(form.atoms):
        if a[0] == 'pair':
            continue
        if a[0] == 'r' and a[1] == 'iso' and a[2] == a[3]:
            t._lc[a] = 0
            continue
        if i in aliases:
            t.var[a] = aliases[i]
        else:
            t.atoms.append(a)
            t.var[a] = len(t.atoms)
        t._lc[a] = t.var[a]
    t.clauses = ClauseStore(clauses)
    return t


def source(name, claims, version='1'):
    return dict(name=name, version=version, claims=[list(x) for x in claims],
                source=dict(SOURCE, reference='independent artificial fixture source '+name))


class RowKnowledgeTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix='algen-row-knowledge-')
        self.addCleanup(self.tmp.cleanup)
        self.path = Path(self.tmp.name)/'values.sqlite'

    def setup_row(self, rows, clauses, queries=None, atoms=None, aliases=None):
        f = fake(rows, atoms)
        q = queries if queries is not None else [((),2*i+j) for i in range(len(f.atoms)) for j in (0,1)]
        p = packed(f,q)
        db = ValueLedger.create(self.path,f,p,[dict(concrete=i) for i in range(len(f.m))],MANIFEST,SOURCE)
        self.addCleanup(db.close)
        t = theory_for(f,clauses,aliases)
        session = FrozenRowTheory(t,f.atoms,'Boolean fixture Theory; no Library math addition')
        self.addCleanup(session.close)
        return f,t,session,db,RowKnowledge(db,session,0)

    def values(self, db):
        row = db.projection().m[0]
        return tuple(True if row[i] else False if row[i+1] else None for i in range(0,len(row),2))

    def test_direct_source_chain_withdraw_restore_reopen_and_public_guard(self):
        f,t,s,db,k = self.setup_row([(True,None,None)],[[-1,2],[-2,3]])
        p = source('p',[(0,True)])
        k.enroll('enroll',[p],0)
        k.derive('r',2,1)
        k.derive('q',1,2)
        self.assertEqual(self.values(db),(True,True,True))
        proofs = [__import__('json').loads(r[0]) for r in db.db.execute('SELECT certificate FROM rk_proofs')]
        self.assertTrue(all([x['literal'] for x in c['core']]==[1] for c in proofs))
        with self.assertRaisesRegex(ValueError,'RowKnowledge'):
            db.apply_row('bypass',dict(concrete=0),np.zeros(6,dtype=bool),SOURCE,3)
        k.withdraw('withdraw','p','1',3)
        self.assertEqual(self.values(db),(None,None,None))
        self.assertEqual([r[0] for r in db.db.execute('SELECT active FROM rk_proofs')],[0,0])
        with ValueLedger(self.path) as other:
            reopened = RowKnowledge(other,s,0)
            receipt = reopened.put_source('restore',p,4)
            self.assertEqual(self.values(other),(True,True,True))
            self.assertFalse(receipt['row_entailment_complete'])
            self.assertTrue(receipt['registered_proof_closure_verified'])
            self.assertEqual(other.summary()['proof_pending'],len(other.conditions()))

    def test_alternative_providers_and_different_cores_are_preserved(self):
        f,t,s,db,k = self.setup_row([(True,None,True)],[[-1,2],[-3,2]])
        p,also_p,r = source('p',[(0,True)]),source('also-p',[(0,True)]),source('r',[(2,True)])
        k.enroll('enroll',[p,also_p,r],0)
        k.register_proof('core-p',s.certificate(1,True,[1]),1)
        k.register_proof('core-r',s.certificate(1,True,[3]),2)
        first = k.withdraw('withdraw-p','p','1',3)
        self.assertEqual(self.values(db),(True,True,True))
        self.assertEqual(first['proofs'][0]['bindings'][0]['providers'],[['also-p','1']])
        second = k.withdraw('withdraw-also-p','also-p','1',4)
        self.assertEqual(self.values(db),(None,True,True))
        self.assertEqual([x['active'] for x in second['proofs']],[False,True])
        k.withdraw('withdraw-r','r','1',5)
        self.assertEqual(self.values(db),(None,None,None))

    def test_all_sources_joint_consistency_versions_replay_and_stale(self):
        f,t,s,db,k = self.setup_row([(True,None)],[[-1,2]])
        p = source('p',[(0,True)])
        first = k.enroll('enroll',[p],0)
        self.assertEqual(k.enroll('enroll',[p],0),dict(first,replayed=True))
        before = list(db.state_rows())
        with self.assertRaisesRegex(ValueError,'compatible'):
            k.put_source('contradiction',source('not-q',[(1,False)]),1)
        self.assertEqual(list(db.state_rows()),before)
        self.assertEqual(db.summary()['revision'],1)
        self.assertEqual(db.db.execute('SELECT count(*) FROM rk_sources').fetchone()[0],1)
        with self.assertRaisesRegex(ValueError,'different claims'):
            k.put_source('overwrite',source('p',[(0,False)]),1)
        with self.assertRaisesRegex(ValueError,'different operation'):
            k.enroll('enroll',[],0)
        with self.assertRaisesRegex(ValueError,'stale'):
            k.derive('stale',1,0)
        k.put_source('version2',source('p',[(0,True)],'2'),1)
        self.assertEqual(db.summary()['revision'],2)  # same bits, new providers

    def test_negative_constant_and_undetermined_are_distinct(self):
        atoms=[('p','p','G'),('p','q','G'),('r','iso',Var('G'),Var('G'))]
        f,t,s,db,k = self.setup_row([(True,None,None)],[[-1,-2]],atoms=atoms)
        p = source('p',[(0,True)])
        k.enroll('enroll',[p],0)
        c = k.derive('negative',1,1)
        self.assertEqual(self.values(db),(True,False,None))
        self.assertEqual(c['outcome'],'derived')
        k.derive('constant',2,2)
        k.withdraw('withdraw','p','1',3)
        self.assertEqual(self.values(db),(None,None,True))
        result = k.derive('not-entailed',1,4)
        self.assertEqual(result['outcome'],'undetermined')
        self.assertEqual(self.values(db),(None,None,True))
        self.assertEqual(db.db.execute('SELECT count(*) FROM rk_proofs').fetchone()[0],2)

    def test_aliases_are_one_literal_but_keep_structural_observations(self):
        f,t,s,db,k = self.setup_row([(True,None,None)],[[-1,2]],aliases={1:1})
        k.enroll('enroll',[source('p',[(0,True)])],0)
        k.derive('alias',1,1)
        self.assertEqual(self.values(db),(True,True,None))
        k.withdraw('withdraw','p','1',2)
        self.assertEqual(self.values(db),(None,None,None))

    def test_invalid_proofs_context_and_unexplained_projection_rejected(self):
        f,t,s,db,k = self.setup_row([(True,None,None)],[[-1,2]])
        with self.assertRaisesRegex(ValueError,'explain'):
            k.enroll('missing-source',[],0)
        self.assertEqual(db.summary()['revision'],0)
        k.enroll('enroll',[source('p',[(0,True)])],0)
        good = s.certificate(1,True,[1])
        invalid=[]
        bad=deepcopy(good);bad['context']='different';invalid.append(bad)
        bad=s.certificate(2,True,[1]);invalid.append(bad)
        bad=deepcopy(good);bad['core'][0]['atom']=['wrong'];invalid.append(bad)
        bad=deepcopy(good);bad['target']=['wrong'];invalid.append(bad)
        for i,c in enumerate(invalid):
            with self.assertRaises(ValueError):k.register_proof('bad'+str(i),c,1)
        self.assertEqual(db.db.execute('SELECT count(*) FROM rk_proofs').fetchone()[0],0)
        changed = FrozenRowTheory(theory_for(f,[[-1,-2]]),f.atoms,'new Theory')
        try:
            with self.assertRaisesRegex(ValueError,'context changed'):RowKnowledge(db,changed,0)
        finally:changed.close()

    def test_source_proof_and_ledger_failure_roll_back_together(self):
        f,t,s,db,k = self.setup_row([(True,None)],[[-1,2]])
        k.enroll('enroll',[source('p',[(0,True)])],0)
        original = db._apply_row_in_transaction
        def interrupt(*args,**kw):
            original(*args,**kw)
            raise KeyboardInterrupt('after data/proof/source writes')
        with patch.object(db,'_apply_row_in_transaction',interrupt):
            with self.assertRaises(KeyboardInterrupt):k.derive('interrupted-proof',1,1)
            with self.assertRaises(KeyboardInterrupt):k.put_source('interrupted-source',source('r',[(1,True)]),1)
        self.assertEqual(db.summary()['revision'],1)
        self.assertEqual(self.values(db),(True,None))
        self.assertEqual(db.db.execute('SELECT count(*) FROM rk_sources').fetchone()[0],1)
        self.assertEqual(db.db.execute('SELECT count(*) FROM rk_proofs').fetchone()[0],0)
        self.assertEqual(db.db.execute('SELECT count(*) FROM rk_events').fetchone()[0],1)

    def test_frozen_clause_edits_and_mutable_metadata_are_rejected(self):
        f,t,s,db,k = self.setup_row([(True,None)],[[-1,2]])
        k.enroll('enroll',[source('p',[(0,True)])],0)
        with self.assertRaises(BufferError):t.clauses.append([1])
        t.clauses.data[0] = 1
        with self.assertRaisesRegex(ValueError,'Theory changed'):k.derive('modified-clause',1,1)
        t.clauses.data[0] = -1
        s.header['reference'] = 'silently changed'
        with self.assertRaisesRegex(ValueError,'Theory changed'):k.derive('modified-metadata',1,1)
        self.assertEqual(db.summary()['revision'],1)

    def test_edit_during_transaction_rolls_back_and_discards_private_solver(self):
        f,t,s,db,k = self.setup_row([(True,None)],[[-1,2]])
        k.enroll('enroll',[source('p',[(0,True)])],0)
        original = db._apply_row_in_transaction
        def edit_after_projection(*args,**kw):
            result = original(*args,**kw)
            t.clauses.data[0] = 1
            return result
        with patch.object(db,'_apply_row_in_transaction',edit_after_projection):
            with self.assertRaisesRegex(ValueError,'Theory changed'):k.derive('edited',1,1)
        self.assertIsNone(s._solver)
        t.clauses.data[0] = -1
        self.assertEqual(db.summary()['revision'],1)
        self.assertEqual(self.values(db),(True,None))
        k.derive('retry',1,1)
        self.assertEqual(self.values(db),(True,True))

    def test_replacing_clause_store_or_backing_arrays_cannot_rebind_proof_context(self):
        f,t,s,db,k = self.setup_row([(True,None)],[[-1,2]])
        k.enroll('enroll',[source('p',[(0,True)])],0)
        original, data, offsets = t.clauses, t.clauses.data, t.clauses.offs
        replacements = [('store',ClauseStore([[-1,-2]])),('data',array('i',[-1,-2])),('offsets',array('q',[0,2]))]
        for name, replacement in replacements:
            if name == 'store':t.clauses = replacement
            elif name == 'data':t.clauses.data = replacement
            else:t.clauses.offs = replacement
            with self.assertRaisesRegex(ValueError,'Theory changed'):
                k.derive('replaced-'+name,1,1)
            t.clauses = original;original.data=data;original.offs=offsets
            self.assertEqual(db.summary()['revision'],1)
            self.assertEqual(self.values(db),(True,None))
        k.derive('original-snapshot',1,1)
        self.assertEqual(self.values(db),(True,True))

    def test_no_public_mutable_solver_and_owner_factory_is_not_proof_basis(self):
        f,t,s,db,k = self.setup_row([(True,None)],[[-1,2]])
        with self.assertRaises(AttributeError):
            s.solver.add_clause([-2])
        def wrong_factory():
            raise AssertionError('mutable Theory factory must not be used')
        t.solver = wrong_factory
        k.enroll('enroll',[source('p',[(0,True)])],0)
        k.derive('original-snapshot',1,1)
        self.assertEqual(self.values(db),(True,True))

    def test_nested_snapshot_guard_cannot_commit_under_temporarily_changed_theory(self):
        f,t,s,db,k = self.setup_row([(True,None)],[[-1,2]])
        with self.assertRaises(AttributeError):
            s.stable()
        with s._stable():
            t.clauses.data[1] = -2
            try:
                with self.assertRaisesRegex(RuntimeError,'reentrant'):
                    k.enroll('nested',[source('p',[(0,True)])],0)
                with self.assertRaisesRegex(ValueError,'Theory changed'):
                    s.derive(1,{1})
            finally:
                t.clauses.data[1] = 2
        self.assertEqual(db.summary()['revision'],0)
        self.assertEqual(db.db.execute('SELECT count(*) FROM rk_rows').fetchone()[0],0)
        k.enroll('enroll',[source('p',[(0,True)])],0)
        k.derive('q',1,1)
        self.assertEqual(self.values(db),(True,True))

    def test_legacy_bridge_collision_cannot_commit_proof_without_row_revision(self):
        f,t,s,db,k = self.setup_row([(True,None)],[[-1,2]])
        p = source('p',[(0,True)])
        # A historical public event can have exactly the metadata/row of a
        # future derivation. It is not a valid retry of that knowledge event.
        metadata = dict(kind='user',reference='RowKnowledge:0:prove-q',context=s.identity,
            active_sources=[dict(name='p',version='1',bundle_sha256=hashlib.sha256(canonical(p).encode()).hexdigest())],
            registered_proofs=[dict(proof=1,active=True,bindings=[dict(literal=1,providers=[['p','1']])])])
        db.apply_row('rk:0:prove-q',dict(concrete=0),np.array([1,0,1,0],dtype=bool),metadata,0)
        db.apply_row('withhold',dict(concrete=0),f.m[0],SOURCE,1)
        k.enroll('enroll',[p],2)
        before = list(db.db.iterdump())
        with self.assertRaisesRegex(ValueError,'collides'):
            k.derive('prove-q',1,3)
        self.assertEqual(list(db.db.iterdump()),before)
        self.assertEqual(self.values(db),(True,None))
        self.assertEqual(db.summary()['revision'],3)
        receipt = k.derive('fresh-proof',1,3)
        self.assertEqual(self.values(db),(True,True))
        self.assertEqual(k.derive('fresh-proof',1,3),dict(receipt,replayed=True))
        self.assertEqual(db.summary()['revision'],4)


if __name__=='__main__':unittest.main()
