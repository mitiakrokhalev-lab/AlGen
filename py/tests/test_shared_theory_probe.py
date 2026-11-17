"""Complete tiny value domains; every source is an artificial assumption."""
from copy import copy,deepcopy
from pathlib import Path
import tempfile
import subprocess
import sys
from types import SimpleNamespace
import unittest
from unittest.mock import patch

from algen.value_ledger import ValueLedger
from test_row_knowledge import theory_for
from test_value_classify import fake,packed
from test_value_ledger import MANIFEST,SOURCE
from tools.probe_shared_theory import PairControl,valid_receipt


class SharedTheoryProbeTest(unittest.TestCase):
    def test_optimized_python_rejected_before_creating_control(self):
        script = """import sys
from tools.probe_shared_theory import PairControl
try:
    PairControl(sys.argv[1],'shared',[('first',2),('second',2)])
except RuntimeError as error:
    sys.exit(0 if str(error) == 'paired external oracles require active assertions' else 2)
sys.exit(3)
"""
        with tempfile.TemporaryDirectory(prefix='algen-shared-optimized-') as root:
            path = Path(root)/'control'
            result = subprocess.run([sys.executable,'-B','-O','-c',script,str(path)],
                cwd=Path(__file__).resolve().parents[1],capture_output=True,timeout=15)
            self.assertEqual(result.returncode,0,result.stderr.decode())
            self.assertFalse(path.exists())

    def fixture(self):
        full = fake([(False,False,False)]*3)
        theory = theory_for(full,[[1,-2],[-2,3]])
        a,b = fake([(False,False)]*3,full.atoms[:2]),fake([(False,False)]*3,full.atoms[1:])
        a.sc = b.sc = SimpleNamespace(T=theory)
        return [(a,packed(a,[((),3),((1,),3)])),(b,packed(b,[((),1),((3,),1)]))],full.atoms[1]

    def run_control(self, root, mode):
        domains,target = self.fixture()
        pair = PairControl(root,mode,[('first',2),('second',2)],row=0,target=target)
        try:
            for sid,(form,conditions) in zip(('first','second'),domains):
                pair.consume(sid,form,conditions,[dict(concrete=i) for i in range(3)],dict(MANIFEST,scheme=sid),SOURCE)
            pair.seal_first_pass()
            return pair.finish()
        finally:pair.abort()

    def test_different_complete_domains_exact_outputs_match_in_separate_and_shared_modes(self):
        with tempfile.TemporaryDirectory(prefix='algen-shared-probe-') as root:
            a=self.run_control(Path(root)/'separate','separate')
            b=self.run_control(Path(root)/'shared','shared')
            self.assertTrue(valid_receipt(a));self.assertTrue(valid_receipt(b))
            self.assertEqual([c['canonical_output_sha256'] for c in a['cases']],[c['canonical_output_sha256'] for c in b['cases']])
            self.assertEqual(sum(x['snapshot_builds'] for x in a['main_basis_stats']),2)
            self.assertEqual(sum(x['snapshot_builds'] for x in b['main_basis_stats']),1)
            self.assertEqual(sum(x['solver_bootstraps'] for x in a['main_basis_stats']),2)
            self.assertEqual(sum(x['solver_bootstraps'] for x in b['main_basis_stats']),1)
            self.assertEqual(b['fresh_validation_basis_stats']['solver_bootstraps'],1)
            self.assertEqual(b['proof_pending'],4)

    def test_receipt_missing_critical_flags_types_proofs_and_timers_is_rejected(self):
        with tempfile.TemporaryDirectory(prefix='algen-shared-receipt-') as root:
            r=self.run_control(Path(root)/'shared','shared')
            self.assertTrue(valid_receipt(r))
            for key in r:
                bad=deepcopy(r);bad.pop(key)
                self.assertFalse(valid_receipt(bad),key)
            for key in r['cases'][0]:
                bad=deepcopy(r);bad['cases'][0].pop(key)
                self.assertFalse(valid_receipt(bad),key)
            for mutate in (lambda x:x.update(proof_pending=True),lambda x:x['cases'][0].update(target_row=False),
                lambda x:x['cases'][0]['updates']['prove']['ledger'].update(row=False),
                lambda x:x['cases'][0]['updates']['prove']['proofs'][0]['bindings'][0].update(literal=True),
                lambda x:x['main_basis_stats'][0].update(solver_bootstraps=2),
                lambda x:x['fresh_validation_basis_stats'].pop('schema_hash_cpu_seconds')):
                bad=deepcopy(r);mutate(bad);self.assertFalse(valid_receipt(bad))

    def test_external_oracle_rejects_ignored_proved_projection(self):
        domains,target=self.fixture()
        original=ValueLedger._apply_row_in_transaction
        def ignored(db,event,identity,row,*args,**kwargs):
            if event.endswith(':canonical-proof'):
                row=row.copy();row[2:4]=False
            return original(db,event,identity,row,*args,**kwargs)
        with tempfile.TemporaryDirectory(prefix='algen-shared-writer-') as root:
            p=PairControl(Path(root)/'shared','shared',[('first',2),('second',2)],row=0,target=target)
            try:
                f,c=domains[0]
                with patch.object(ValueLedger,'_apply_row_in_transaction',ignored),self.assertRaises(AssertionError):
                    p.consume('first',f,c,[dict(concrete=i) for i in range(3)],MANIFEST,SOURCE)
            finally:p.abort()

    def test_missing_reordered_truncated_or_other_owner_domains_cannot_finish(self):
        domains,target=self.fixture()
        with tempfile.TemporaryDirectory(prefix='algen-shared-domain-') as root:
            p=PairControl(Path(root)/'shared','shared',[('first',2),('second',2)],row=0,target=target)
            try:
                f,c=domains[0]
                with self.assertRaisesRegex(ValueError,'reordered'):
                    p.consume('second',f,c,[dict(concrete=i) for i in range(3)],MANIFEST,SOURCE)
                with self.assertRaisesRegex(ValueError,'incomplete'):
                    p.consume('first',f,packed(f,[((),3)]),[dict(concrete=i) for i in range(3)],MANIFEST,SOURCE)
                p.consume('first',f,c,[dict(concrete=i) for i in range(3)],MANIFEST,SOURCE)
                with self.assertRaisesRegex(ValueError,'both complete'):p.finish()
                f,c=domains[1]
                f.sc=SimpleNamespace(T=copy(f.sc.T))
                with self.assertRaisesRegex(ValueError,'exact unchanged Theory owner'):
                    p.consume('second',f,c,[dict(concrete=i) for i in range(3)],MANIFEST,SOURCE)
            finally:p.abort()


if __name__=='__main__':unittest.main()
