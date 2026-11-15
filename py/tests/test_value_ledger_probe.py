"""No Library/GAP: the probe must validate its own complete-domain receipt."""
from copy import deepcopy
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from test_value_classify import fake, packed
from test_value_ledger import MANIFEST, SOURCE
from algen.value_ledger import ValueLedger
from tools.probe_value_ledger import probe, valid_receipt


class ValueLedgerProbeTest(unittest.TestCase):
    def test_full_small_projection_control_and_fail_closed_receipt(self):
        form = fake([(True, True), (False, True), (True, False)])
        conditions = packed(form, [((1,), 2), ((3,), 0)])
        with tempfile.TemporaryDirectory(prefix='algen-ledger-probe-') as tmp:
            receipt = probe(form, conditions, [dict(concrete=i) for i in range(3)],
                            MANIFEST, SOURCE, Path(tmp)/'private-db')
            self.assertTrue(valid_receipt(receipt))
            for key in ('sampled', 'full_domain_oracles_equal', 'candidate_frontier_complete',
                        'proof_pending', 'initial_state_sha256', 'database_files_uploaded',
                        'rows', 'literal_columns', 'domain_sha256', 'input_projection_sha256',
                        'input_conditions_sha256', 'initial', 'restored', 'database_files',
                        'hot_conditions_after_hide', 'production_speedup_claimed', 'version', 'scope'):
                bad = deepcopy(receipt)
                bad.pop(key)
                self.assertFalse(valid_receipt(bad), key)
            for key, val in [('classified', True), ('classified', 0), ('initial_state_sha256', None)]:
                bad = deepcopy(receipt); bad[key] = val
                self.assertFalse(valid_receipt(bad), key)
            for mutate in ('missing', 'not_all', 'both_absent'):
                bad = deepcopy(receipt)
                if mutate == 'missing':
                    bad['updates'][2].pop('affected_conditions')
                elif mutate == 'not_all':
                    bad['updates'][2]['affected_conditions'] -= 1
                else:
                    bad['state_hashes'].pop('restored'); bad['state_hashes'].pop('new_row_restored')
                self.assertFalse(valid_receipt(bad), mutate)
            for kinds in ({'ABCR': 2}, {'': 2}, {'R': 1, 'C': 1}):
                bad = deepcopy(receipt)
                bad['initial']['kinds'] = kinds
                bad['restored']['kinds'] = kinds
                self.assertFalse(valid_receipt(bad), kinds)

    def test_oracle_detects_requested_mask_not_applied_to_database(self):
        form = fake([(True, True), (False, True), (True, False)])
        conditions = packed(form, [((1,), 2), ((3,), 0)])
        original = ValueLedger.apply_row
        def ignored_mask(db, event, identity, row, source, revision, **kw):
            if event == 'hide-checked-cell':
                # A broken writer still returns a plausible update receipt.
                row = form.m[identity['concrete']]
            return original(db, event, identity, row, source, revision, **kw)
        with tempfile.TemporaryDirectory(prefix='algen-ledger-bad-writer-') as tmp:
            with patch.object(ValueLedger, 'apply_row', ignored_mask), self.assertRaises(AssertionError):
                probe(form, conditions, [dict(concrete=i) for i in range(3)],
                      MANIFEST, SOURCE, Path(tmp)/'private-db')


if __name__ == '__main__':
    unittest.main()
