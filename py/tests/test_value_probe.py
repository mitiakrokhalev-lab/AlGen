"""The real-table probe keeps verdicts and source inputs unchanged."""
from copy import deepcopy
import unittest
from algen.conditions import PackedConditions
from tools.probe_value_classify import probe,valid_receipt
from test_value_tasks import fake


class ValueProbeTest(unittest.TestCase):
    def test_all_verdicts_and_kept_cross_tab_and_source_immutability(self):
        f=fake([(None,True,False),(True,True,True)])
        report=[{'_cols':[0,5],'вердикт':'неизвестно','свёрнута':True},
                {'_cols':[4,1],'вердикт':'выводится'},
                {'вердикт':'выводится','цель':'unconditional fact'}]
        before=deepcopy(report);matrix=f.m.copy()
        mins=PackedConditions(6,3,2)
        mins[((0,),4)]=0
        mins[((4,),0)]=0
        r=probe(f,mins,report,100)
        self.assertTrue(r['exact_output'])
        self.assertEqual(r['classified'],2)
        self.assertEqual(r['sampled_minimals'],2)
        self.assertEqual(r['report_rows_without_cols'],1)
        self.assertEqual(r['kinds'],{'A':1,'C':1})
        self.assertEqual(r['kept_kinds'],{'C':1})
        self.assertEqual(r['kind_by_verdict'],{'A / неизвестно':1,'C / выводится':1})
        self.assertEqual(report,before)
        self.assertTrue((f.m==matrix).all())
        self.assertTrue(valid_receipt(r,2))
        for key,value in [('exact_output',False),('classified',0),('engine_sha256','bad'),('kinds',{'A':3})]:
            bad=dict(r);bad[key]=value
            self.assertFalse(valid_receipt(bad,2))

    def test_reference_guard_rejects_duplicate_fixed_and_pairs(self):
        f=fake([(None,True,False)]);f.fixed=[0]
        with self.assertRaisesRegex(ValueError,'unique primitive'):
            probe(f,{},[{'_cols':[0,5],'вердикт':'неизвестно'}],1)
        f.atoms.append(('pair','a','G','H',True))
        with self.assertRaisesRegex(ValueError,'unique primitive'):
            probe(f,{},[],0)


if __name__=='__main__':unittest.main()
