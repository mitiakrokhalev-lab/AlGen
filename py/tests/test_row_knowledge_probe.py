"""Full tiny saved domains and external-oracle failures; no new group data."""
from copy import deepcopy
from pathlib import Path
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

import numpy as np

from algen.value_ledger import ValueLedger
from test_row_knowledge import theory_for
from test_value_classify import fake, packed
from test_value_ledger import MANIFEST, SOURCE
from tools.probe_row_knowledge import probe, valid_receipt


class RowKnowledgeProbeTest(unittest.TestCase):
    def fixture(self):
        form = fake([(True,True),(True,True),(False,True)])
        form.m = np.asfortranarray(form.m)
        form.sc = SimpleNamespace(T=theory_for(form,[[-1,2]]))
        return form,packed(form,[((),2),((0,),2)])

    def test_complete_saved_codes_proof_withdraw_and_fresh_solver_reopen(self):
        form,conditions = self.fixture()
        with tempfile.TemporaryDirectory(prefix='algen-knowledge-probe-') as tmp:
            r = probe(form,conditions,[dict(concrete=i) for i in range(3)],MANIFEST,SOURCE,Path(tmp)/'db')
            self.assertTrue(valid_receipt(r))
            self.assertEqual(r['classified'],2)
            self.assertEqual(r['target_atom'],1)
            self.assertEqual(r['source_claims'],1)
            self.assertEqual(r['selection_trials'],1)
            self.assertEqual([x['literal'] for x in r['proof_certificate']['core']],[1])
            self.assertEqual(r['initial']['kinds'],{'A':2})
            self.assertEqual(r['restored']['kinds'],{'C':2})
            for key in r:
                bad = deepcopy(r);bad.pop(key)
                self.assertFalse(valid_receipt(bad),key)
            for key,value in [('classified',True),('selection_trials',0),('proof_pending',0),
                              ('database_files_uploaded',True),('mathematical_provenance_audited',True)]:
                bad=deepcopy(r);bad[key]=value
                self.assertFalse(valid_receipt(bad),key)
            for key in ('derived','restored','masked','withdrawn'):
                bad=deepcopy(r);bad['state_hashes'].pop(key)
                self.assertFalse(valid_receipt(bad),key)
            mutations = [lambda c:c.update(core=[None]),lambda c:c.pop('target'),
                lambda c:c['core'][0].pop('atom'),lambda c:c['core'].append(deepcopy(c['core'][0])),
                lambda c:c['core'][0].update(literal=True),lambda c:c['core'][0].update(value=1),
                lambda c:c.update(atom=True)]
            for mutate in mutations:
                bad=deepcopy(r);mutate(bad['proof_certificate'])
                self.assertFalse(valid_receipt(bad))
            bad=deepcopy(r);bad['updates']['derive']['ledger']['row']=False
            self.assertFalse(valid_receipt(bad))

    def test_external_oracle_rejects_writer_ignoring_proved_projection(self):
        form,conditions = self.fixture()
        original = ValueLedger._apply_row_in_transaction
        def ignore_proof(db,event,identity,row,*args,**kw):
            if event.endswith(':derive-known-hidden-value'):
                row=row.copy();row[2:4]=False
            return original(db,event,identity,row,*args,**kw)
        with tempfile.TemporaryDirectory(prefix='algen-knowledge-bad-writer-') as tmp:
            with patch.object(ValueLedger,'_apply_row_in_transaction',ignore_proof),self.assertRaises(AssertionError):
                probe(form,conditions,[dict(concrete=i) for i in range(3)],MANIFEST,SOURCE,Path(tmp)/'db')


if __name__=='__main__':unittest.main()
