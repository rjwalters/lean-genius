"""Runner checks on tiny fixtures. These are NOT the graph positive controls."""
import argparse
import contextlib
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import runner as r


class RunnerTests(unittest.TestCase):
    def test_scope(self):
        for n, d, m in [(48, 7, 24), (63, 8, 21), (63, 8, 63), (80, 9, 2), (78, 9, 3)]:
            r.scope(n, d, m)
        for values in [(81, 9, 3), (80, 9, 80), (80, 9, 1), (120, 11, 2), (49, 7, 7)]:
            with self.assertRaises(ValueError):
                r.scope(*values)

    def test_retry_and_budget(self):
        ledger = {'runs': [], 'controls': {}}
        self.assertEqual(r.policy(ledger, 48, 7, 24, 'h', 0, False), ('control', 3600))
        with self.assertRaises(ValueError):
            r.policy(ledger, 80, 9, 2, 'h', 0, False)
        prior = dict(n=48, d=7, m=24, status='UNKNOWN', kind='control', cnf={'sha256': 'h'}, metadata={'sha256':'map'}, seed=0, wall_seconds=3600)
        ledger['runs'] = [prior]
        self.assertEqual(r.policy(ledger, 48, 7, 24, 'h', 0, True, 'map'), ('control', 14400))
        for meta in [None, 'changed-map']:
            with self.assertRaises(ValueError):
                r.policy(ledger, 48, 7, 24, 'h', 0, True, meta)
        for h, seed, retry in [('h', 0, False), ('changed', 0, True), ('h', 1, True)]:
            with self.assertRaises(ValueError):
                r.policy(ledger, 48, 7, 24, h, seed, retry)
        for status in ['RUNNING', 'PREPARED', 'SAT', 'UNSAT', 'ERROR']:
            prior['status'] = status
            with self.assertRaises(ValueError):
                r.policy(ledger, 48, 7, 24, 'h', 0, True)
        prior.update(status='UNKNOWN', wall_seconds=r.BUDGET)
        with self.assertRaises(ValueError):
            r.policy(ledger, 48, 7, 24, 'h', 0, True)

    def test_first_sat_stop(self):
        ledger = {'runs': [dict(kind='q9', status='SAT')], 'controls': {}}
        with self.assertRaises(ValueError):
            r.policy(ledger, 48, 7, 24, 'h', 0, False)

    def exercise(self, tmp, formula, expected, fake=None):
        root = Path(tmp)
        cnf = root / 'fixture.cnf'
        cnf.write_text(formula)
        meta = root / 'fixture.json'
        meta.write_text('{"fixture_only": true}')
        args = argparse.Namespace(n=48, d=7, m=24, cnf=str(cnf), metadata=str(meta), seed=0, retry=False)
        ledger = {'runs': [], 'controls': {}}
        path = root / 'ledger.json'
        with patch.object(r, 'ROOT', root), contextlib.redirect_stdout(io.StringIO()):
            if fake:
                with patch.object(r, 'KISSAT', fake), patch.object(r, 'policy', return_value=('control', 1)):
                    r.run(args, ledger, path)
            else:
                r.run(args, ledger, path)
        result = json.loads(path.read_text())['runs'][0]
        self.assertEqual(result['status'], expected)
        self.assertFalse(result['proof_logging'])
        self.assertEqual(len([x for x in result['command'][1:] if not x.startswith('-')]), 1)
        self.assertGreater(result['wall_seconds'], 0)
        self.assertTrue((Path(result['directory']) / 'result.json').exists())
        self.assertEqual(ledger['controls'], {})
        return result

    def test_real_kissat_sat(self):
        with tempfile.TemporaryDirectory() as tmp:
            result = self.exercise(tmp, 'p cnf 2 2\n1 0\n-1 2 0\n', 'SAT')
            self.assertEqual(result['model_check']['status'], 'PASS')

    def test_real_kissat_unsat(self):
        with tempfile.TemporaryDirectory() as tmp:
            self.exercise(tmp, 'p cnf 1 2\n1 0\n-1 0\n', 'UNSAT')

    def test_wall_cap_kills_own_process(self):
        with tempfile.TemporaryDirectory() as tmp:
            fake = Path(tmp) / 'sleeping-solver'
            fake.write_text('#!/usr/bin/env python3\nimport sys,time\nif "--version" in sys.argv: print("fixture")\nelse: time.sleep(30)\n')
            fake.chmod(0o755)
            result = self.exercise(tmp, 'p cnf 1 1\n1 0\n', 'UNKNOWN', fake)
            self.assertEqual(result['termination_reason'], 'wall cap')
            self.assertLess(result['wall_seconds'], 5)
            import os
            with self.assertRaises(ProcessLookupError):
                os.kill(result['pid'], 0)

    def test_sat_observed_despite_timeout_or_bad_exit(self):
        for ending, expected in [('time.sleep(30)', 'UNKNOWN'), ('sys.exit(1)', 'ERROR')]:
            with tempfile.TemporaryDirectory() as tmp:
                fake = Path(tmp) / 'sat-then-incomplete-exit'
                fake.write_text('#!/usr/bin/env python3\nimport sys,time\nif "--version" in sys.argv: print("fixture")\nelse:\n print("s SATISFIABLE",flush=True)\n print("v 1 0",flush=True)\n '+ending+'\n')
                fake.chmod(0o755)
                result = self.exercise(tmp, 'p cnf 1 1\n1 0\n', expected, fake)
                self.assertTrue(result['sat_observed'])
                self.assertEqual(result['model_check']['status'], 'PASS')
                result['kind'] = 'q9'
                ledger = {'runs':[result], 'controls':{}}
                with self.assertRaises(ValueError):
                    r.policy(ledger, 63, 8, 21, 'new', 0, False, 'map')

    def test_invalid_model(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            cnf, log = root / 'f.cnf', root / 'f.log'
            cnf.write_text('p cnf 2 1\n1 0\n')
            for model in ['v -1 2 0\n', 'v 1 0\n', 'v 1 -1 2 0\n']:
                log.write_text(model)
                with self.assertRaises(ValueError):
                    r.check_model(cnf, log)


if __name__ == '__main__':
    unittest.main(verbosity=2)
