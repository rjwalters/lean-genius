import contextlib
import io
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

import dispatch_h1_residual_verdict_only as target


class H1ResidualTests(unittest.TestCase):
    def setUp(self):
        self.root = Path(__file__).resolve().parent.parent
        self.config = self.root/'phase_b_h1_verdict_20260916/config.draft.json'

    def test_exact_real_census_and_two_solver_policy(self):
        plan, cases = target.select(self.config)
        self.assertEqual(len(plan['cases']), 1416)
        self.assertEqual(len(plan['historical']), 96)
        self.assertEqual(len(cases), 1161)
        self.assertTrue(all(c['sector'] == 'H1' and c['policy'] ==
            {'crosscheck': True, 'primary_cap_seconds': 14400,
             'crosscheck_cap_seconds': 14400} for c in cases))
        self.assertFalse({c['id'] for c in cases} & {r['id'] for r in plan['historical']})

    def test_wrapper_and_cap_drift_rejected(self):
        with tempfile.TemporaryDirectory() as temp:
            path = Path(temp)/'config.json'
            config = json.loads(self.config.read_text())
            # The source paths in the real config are relative to its directory.
            config['index']['path'] = str(self.root/'phase_b_survivors_20260910.json')
            config['historical_overlay']['path'] = str(self.root/'phase_b_historical_overlay_96/historical-96.json')
            config['h1_residual']['wrapper_sha256'] = '0'*64
            path.write_text(json.dumps(config))
            with self.assertRaisesRegex(ValueError, 'wrapper identity'):
                target.select(path)
            config['h1_residual']['wrapper_sha256'] = json.loads(self.config.read_text())['h1_residual']['wrapper_sha256']
            config['policies']['H1']['crosscheck'] = False
            path.write_text(json.dumps(config))
            with self.assertRaisesRegex(ValueError, 'two-solver cap'):
                target.select(path)

    def test_dry_run_selects_only_residual_and_rejects_historical_pilot(self):
        plan, cases = target.select(self.config)
        output = io.StringIO()
        with patch.object(sys, 'argv', ['wrapper', '--config', str(self.config)]), contextlib.redirect_stdout(output):
            self.assertEqual(target.main(), 0)
        summary = json.loads(output.getvalue())
        self.assertEqual((summary['inventory_cases'], summary['selected_cases'],
                          summary['historical_evidence_cases']), (1416, 1161, 96))
        historical = plan['historical'][0]['id']
        with patch.object(sys, 'argv', ['wrapper', '--config', str(self.config), '--case-id', historical]):
            with self.assertRaises(SystemExit):
                target.main()
        pilot = json.loads((self.root/'phase_b_h1_verdict_20260916/pilot-24.json').read_text())
        self.assertEqual(len(pilot['cases']), 24)
        self.assertEqual({r['id'] for r in pilot['cases']} <= {r['id'] for r in cases}, True)
        pilot_path=self.root/'phase_b_h1_verdict_20260916/pilot-24.json'
        output=io.StringIO()
        with patch.object(sys,'argv',['wrapper','--config',str(self.config),'--pilot',str(pilot_path)]), contextlib.redirect_stdout(output):
            self.assertEqual(target.main(),0)
        self.assertEqual(json.loads(output.getvalue())['selected_cases'],24)
        with tempfile.TemporaryDirectory() as temp:
            changed=Path(temp)/'pilot.json';pilot['config_sha256']='0'*64;changed.write_text(json.dumps(pilot))
            with self.assertRaisesRegex(ValueError,'Pilot configuration identity'):
                target.pilot_ids(changed,self.config,cases)


if __name__ == '__main__':
    unittest.main()
