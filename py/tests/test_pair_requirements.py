"""Paired explicit normality must define both quotient terms in k<=3/s<=2."""

from types import SimpleNamespace
import unittest
from unittest.mock import patch

import numpy as np

from algen import enumerate as E
from algen import native_enum as N
from algen import table as T
from algen.etalon import scheme,term
from algen.logic import Vocab


def fixture(rows=None):
    v = Vocab.section('grp')
    g,_,_ = scheme(v,{'раздел':'grp','условие':'∀ G : Grp; ∀ H : Sub(G); ∀ K : Sub(G)'})
    names = {str(t):t for t in g.terms}
    G,H,K = (names[x] for x in ('G','H','K'))
    QH,QK = (term(g,x,names,'grp') for x in ('quotient(G,H)','quotient(G,K)'))
    atoms = [('p','normal',H),('p','normal',K),('r','le',H,K),('p','cyclic',QH),('p','cyclic',QK)]
    # Concrete compatible examples, not arbitrary SAT models:
    # C2,H=K=1; V4,H=C2,K=1; V4,H=K=1; S3,H=1,K=C2.
    rows = rows if rows is not None else [(True,True,True,True,True),(True,True,False,True,False),
            (True,True,True,False,False),(True,False,True,False,None)]
    m = np.zeros((len(rows),2*len(atoms)),dtype=bool)
    for i,row in enumerate(rows):
        for j,value in enumerate(row):
            if value is not None:
                m[i,2*j+(0 if value else 1)] = True
    f = SimpleNamespace(g=g,atoms=atoms,index={a:i for i,a in enumerate(atoms)},
                        m=m,s=m.copy(),e=m.copy(),fixed=[],req={3:{0},4:{2}},need=[{3},{4}])
    f.lit = lambda j:E.Form.lit(f,j)
    f.lits = lambda j:E.Form.lits(f,j)
    E.add_pairs(f,[(H,K)])
    return f


class PairRequirementTest(unittest.TestCase):
    def test_pair_provides_both_requirements_python_and_native(self):
        self.assertIsNotNone(N.library(),N._unavailable)
        for native in (False,True):
            for vec in (False,True):
                for prune in (False,True):
                    with self.subTest(native=native,vec=vec,prune=prune),patch.object(E,'NATIVE_ENUM',native), \
                         patch.object(E,'VEC',vec),patch.object(E,'PRUNE_FREE',prune):
                        f = fixture()
                        alive,_ = E.enumerate_form(f,3)
                        self.assertIn(((4,6,10),8),alive)
                        self.assertIn(((4,6,10),8),E.pair_minimal(f,E.minimal(alive)))
                        if native and vec:
                            self.assertTrue(f.enumeration_engine.startswith('cpp:'))

    def test_half_removal_cannot_destroy_definedness(self):
        f = fixture()
        original = {((4,6,10),8):1}
        self.assertEqual(E.pair_minimal(f,original),original)

    def test_negative_normality_pair_does_not_define_quotients(self):
        for native in (False,True):
            with self.subTest(native=native),patch.object(E,'NATIVE_ENUM',native):
                alive,_ = E.enumerate_form(fixture(),3)
                self.assertNotIn(((4,6,12),8),alive)
                # S3,H=K=C2: the negative-normality pair really holds, while
                # both quotient properties are undefined, never False.
                f = fixture([(False,False,True,None,None)])
                f.need = []
                alive,_ = E.enumerate_form(f,1)
                self.assertNotIn(((12,),6),alive)
                self.assertNotIn(((12,),8),alive)

    def test_providers_keep_polarities_and_not_both_supplies_nothing(self):
        self.assertEqual(E.pair_requirement_providers(fixture()),{10:(0,2),12:(1,3)})

    def test_abstract_partial_matrices_python_native_all_outputs(self):
        # Boolean stress fixtures, not asserted to be concrete group examples.
        rng = np.random.default_rng(7321)
        for case in range(25):
            raw = rng.integers(0,3,size=(8,5))
            rows = [[None if v==2 else bool(v==0) for v in row] for row in raw]
            results = []
            for native in (False,True):
                with patch.object(E,'NATIVE_ENUM',native):
                    f = fixture(rows)
                    alive,empty = E.enumerate_form(f,3)
                    results.append((list(alive.items()),empty,f.n_alive,list(E.pair_minimal(f,E.minimal(alive)).items())))
            self.assertEqual(results[0],results[1],case)

    def test_completed_paired_report_fingerprint_changes_without_library_rebuild(self):
        with patch.object(T,'_fp',return_value='same-library'):
            self.assertEqual(T.result_fp('G',3),'same-library:3')
            self.assertEqual(T.result_fp('GHK',3),'same-library:3:pair-req:1')
            self.assertEqual(T.result_fp('AB','3/2',.1),'same-library:3/2:d0.1:pair-req:1')


if __name__=='__main__':
    unittest.main()
