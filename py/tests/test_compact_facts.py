"""Full report parity and bounded fact-solver numbering with sparse global IDs."""
import copy
import unittest
from unittest.mock import patch

from pysat.solvers import Solver as RealSolver
from algen import compress as C
from test_compress import FakeForm, row


class CompactFactsTest(unittest.TestCase):
    def form_rows(self, signed=False):
        atoms = list('abcde')
        form = FakeForm(atoms, [['a','b'] if signed else ['-a','b'], ['-b','c']],
                        fixed=[('d',False)] if signed else ())
        ids = [101,1000,2001,4000,5003]
        form.sc.T.v = dict(zip(atoms,ids))
        form.sc.T.clauses = [[ids[abs(l)-1]*(1 if l>0 else -1) for l in clause]
                            for clause in form.sc.T.clauses]
        rows = [row(form,['a'],'b',kind='выводится',n=10),
                row(form,['b'],'c',kind='выводится',n=9),
                row(form,['a'],'c',kind='выводится',n=1),
                row(form,['e'],'a',kind='неизвестно',n=2)]
        if signed:
            for r in (rows[0],rows[2]):
                r['_cols'][0] ^= 1
                r['посылки'] = ['¬a']
                r['класс'] = ('¬a',r['класс'][-1])
        for r in rows:r['запрет']=list(r['класс'])
        return form, rows

    def compare(self,signed):
        form, rows = self.form_rows(signed)
        outputs, sizes = [], []
        for compact in (False,True):
            created = []
            class Observed:
                def __init__(self,*args,**kwargs):
                    self.s = RealSolver(*args,**kwargs)
                    self.max_vars = None
                    created.append(self)
                def __getattr__(self,name):return getattr(self.s,name)
                def delete(self):
                    self.max_vars = self.s.nof_vars()
                    self.s.delete()
            result = copy.deepcopy(rows)
            with patch.object(C,'COMPACT_FACTS',compact), patch('pysat.solvers.Solver',Observed):
                C.compress(form,result,use_instances=False)
            self.assertEqual(C.verify(form,result),[])
            outputs.append(result);sizes.append(created[0].max_vars)
        self.assertEqual(outputs[0],outputs[1])
        self.assertGreater(sizes[0],4000)
        self.assertLess(sizes[1],32)

    def test_same_full_report_and_bounded_variables(self):self.compare(False)
    def test_signed_forbids_and_negative_fixed(self):self.compare(True)

    def test_interrupted_fact_mapping_closes_both_owned_solvers(self):
        form,rows=self.form_rows()
        opened=[]
        class Owned:
            def __init__(self,*args,**kwargs):
                self.s=RealSolver(*args,**kwargs);self.closed=False;opened.append(self)
            def __getattr__(self,name):return getattr(self.s,name)
            def delete(self):self.closed=True;self.s.delete()
        original=C._safe_forbid;calls=0
        def interrupted(*args):
            nonlocal calls
            calls+=1
            if calls==len(rows)+1:raise TimeoutError('interrupted during compact map')
            return original(*args)
        with patch.object(C,'COMPACT_FACTS',True),patch.object(C,'PRECHECK',False), \
             patch.object(form.sc.T,'solver',side_effect=lambda:Owned(name='g4',bootstrap_with=form.sc.T.clauses)), \
             patch('pysat.solvers.Solver',Owned),patch.object(C,'_safe_forbid',side_effect=interrupted):
            with self.assertRaises(TimeoutError):C.compress(form,rows,use_instances=False)
        self.assertEqual(len(opened),2)
        self.assertTrue(all(s.closed for s in opened))


if __name__=='__main__':unittest.main()
