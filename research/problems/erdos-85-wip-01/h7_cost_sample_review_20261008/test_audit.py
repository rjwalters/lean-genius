"""Receipt mutations only; no CNF generation, cloud, solver or Lean execution."""
import copy
import json
from pathlib import Path
import unittest

import audit_sample


class ReceiptAudit(unittest.TestCase):
    def setUp(self):
        path = Path(__file__).parent / 'reviewed/receipts/sample_results.jsonl'
        rows = [json.loads(line) for line in path.read_text().splitlines()]
        self.good = next(r for r in rows if r['kind'] == 'leaf' and r['status'] == 'CERTIFIED')
        self.timeout = next(r for r in rows if r['status'] == 'SOLVER_TIMEOUT')

    def check(self, record):
        audit_sample.check_result(record, self.good['cnf_sha256'], self.good['cnf_bytes'], self.good['units'])

    def test_real_receipt_fields(self):
        self.check(self.good)
        r = self.timeout
        audit_sample.check_result(r, r['cnf_sha256'], r['cnf_bytes'], r['units'])

    def test_identity_mutations(self):
        for key, value in [('cnf_sha256', '0' * 64), ('expected_cnf_sha256', '0' * 64),
                           ('cnf_bytes', 0), ('units', []), ('seed', 1), ('cap_seconds', 7200)]:
            with self.subTest(key=key):
                r = copy.deepcopy(self.good)
                r[key] = value
                with self.assertRaises(ValueError):
                    self.check(r)

    def test_process_and_binary_mutations(self):
        for section, key, value in [('solver', 'returncode', 0), ('solver', 'unsat_line', False),
                                    ('checker', 'returncode', 1), ('checker', 'verified_line', False),
                                    ('checker', 'heap_mb', 8000), ('checker', 'cpu_seconds', float('nan')),
                                    ('proof', 'checker_closed_early', True), ('proof', 'sha256', 'bad'),
                                    ('binaries', 'cake_lpr', '0' * 64), ('binaries', 'cadical', '0' * 64)]:
            with self.subTest(section=section, key=key):
                r = copy.deepcopy(self.good)
                r[section][key] = value
                with self.assertRaises(ValueError):
                    self.check(r)

    def test_timeout_cannot_be_promoted(self):
        r = copy.deepcopy(self.timeout)
        r['status'] = 'CERTIFIED'
        with self.assertRaises(ValueError):
            audit_sample.check_result(r, r['cnf_sha256'], r['cnf_bytes'], r['units'])

    def test_archival_transform_preserves_all_substantive_fields(self):
        original = copy.deepcopy(self.timeout)
        original.pop('sampler', None)
        original['logs'] = {'cadical.log': 'x' * 2500 + 'y' * 1500, 'cake_lpr.log': 'diagnostic'}
        changed = audit_sample.committed_view(original, 1)
        self.assertEqual(changed['logs'], {'cadical.log': 'y' * 1500, 'cake_lpr.log': 'diagnostic'})
        self.assertEqual(changed['sampler'], 'main')
        self.assertEqual(changed['duplicate_runs_same_proof'], 1)
        for key in ('status', 'solver', 'checker', 'proof', 'cnf_sha256', 'units'):
            self.assertEqual(changed[key], original[key])
        self.assertEqual(len(original['logs']['cadical.log']), 4000)


if __name__ == '__main__':
    unittest.main(verbosity=2)
