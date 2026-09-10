import concurrent.futures
import hashlib
import json
from pathlib import Path
import tempfile
import threading
import time
import unittest
from unittest.mock import patch
from types import SimpleNamespace
import dispatch_verdict_only as d


class DispatcherTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(); self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        d.runner.ABORT.clear()
        self.addCleanup(d.runner.ABORT.clear)
        self.disk = patch.object(d.shutil, 'disk_usage', return_value=SimpleNamespace(free=20*1024**3))
        self.disk.start(); self.addCleanup(self.disk.stop)
        self.plan = {'captured': [], 'config': {'index': {'sha256': 'a'*64}}}
        self.case = {'id': 'case1', 'sector': 'H5', 'policy': {
            'crosscheck': True, 'primary_cap_seconds': 2, 'crosscheck_cap_seconds': 2}}
        self.binary = self.root / 'solver'
        self.binary.write_text('#!/usr/bin/env python3\nprint("s UNSATISFIABLE")\nraise SystemExit(20)\n')
        self.binary.chmod(0o755)

    def prepare(self, case, plan, directory):
        cnf = directory / 'input.cnf'; cnf.write_text('p cnf 1 1\n1 0\n')
        return {'id': case['id'], 'sector': case['sector'], 'cnf_path': str(cnf),
                'cnf_sha256': d.runner.sha256(cnf), 'generator_commit': 'b'*40, 'generated': True}

    def run_case(self, prep=None):
        with patch.object(d, 'prepare', side_effect=prep or self.prepare):
            return d.run_prepared_case(self.case, self.plan, self.root, self.binary, self.binary)

    def test_real_fake_process_crosscheck_and_owned_cleanup(self):
        result = self.run_case()
        self.assertEqual(result['status'], 'UNSAT_CROSSCHECKED')
        self.assertTrue(result['generated_input_removed'])
        self.assertFalse((self.root/'case1/input.cnf').exists())
        self.assertTrue((self.root/'case1/preparation.json').exists())
        self.assertTrue((self.root/'case1/solve/case1/result.json').exists())

    def test_existing_case_directory_untouched(self):
        directory = self.root/'case1'; directory.mkdir()
        receipt = directory/'result.json'; receipt.write_bytes(b'old evidence')
        result = self.run_case()
        self.assertEqual(result['status'], 'ERROR')
        self.assertEqual(receipt.read_bytes(), b'old evidence')

    def test_sat_input_preserved(self):
        self.binary.write_text('#!/usr/bin/env python3\nprint("s SATISFIABLE")\nraise SystemExit(10)\n')
        result = self.run_case()
        self.assertEqual(result['status'], 'SAT_CANDIDATE')
        self.assertTrue((self.root/'case1/input.cnf').exists())

    def test_existing_input_never_removed(self):
        def prep(*args):
            value = self.prepare(*args); value['generated'] = False; return value
        result = self.run_case(prep)
        self.assertEqual(result['status'], 'UNSAT_CROSSCHECKED')
        self.assertTrue((self.root/'case1/input.cnf').exists())

    def test_cancel_after_preparation_no_solver(self):
        def prep(*args):
            value = self.prepare(*args); d.runner.ABORT.set(); return value
        with patch.object(d.runner, 'run_case') as solve:
            result = self.run_case(prep)
        solve.assert_not_called()
        self.assertEqual(result['status'], 'ERROR')
        self.assertTrue((self.root/'case1/input.cnf').exists())

    def test_dependency_mutation_after_preparation_no_solver(self):
        dep = self.root/'dependency'; dep.write_bytes(b'banked')
        self.plan['captured'] = [(dep, b'banked')]
        def prep(*args):
            value = self.prepare(*args); dep.write_bytes(b'changed'); return value
        with patch.object(d.runner, 'run_case') as solve:
            result = self.run_case(prep)
        solve.assert_not_called(); self.assertEqual(result['status'], 'ERROR')

    def test_generation_failure_receipted(self):
        def prep(*args): raise RuntimeError('generation failed')
        result = self.run_case(prep)
        self.assertEqual(result['status'], 'ERROR')
        self.assertIn('generation failed', json.loads((self.root/'case1/result.json').read_text())['error'])

    def test_unknown_retained_receipt_but_fresh_input_removed(self):
        self.binary.write_text('#!/usr/bin/env python3\nprint("s UNKNOWN")\n')
        result = self.run_case()
        self.assertEqual(result['status'], 'UNKNOWN')
        self.assertTrue(result['generated_input_removed'])

    def test_completed_error_batch_prevents_refill(self):
        calls = []
        def worker(case):
            calls.append(case['id']); return {'id': case['id'], 'status': 'ERROR' if case['id']=='bad' else 'UNSAT_CROSSCHECKED'}
        def all_done(pending, **kwargs):
            done, rest = concurrent.futures.wait(pending)
            return sorted(done, key=lambda f: f.result()['status']=='ERROR'), rest
        state = {'results': []}
        original_wait = concurrent.futures.wait
        def controlled_wait(pending, **kwargs):
            done, rest = original_wait(pending)
            return sorted(done, key=lambda f: f.result()['status']=='ERROR'), rest
        with patch.object(d.futures, 'wait', side_effect=controlled_wait):
            d.dispatch([{'id': x} for x in ['good','bad','third']], worker, 2, self.root, state)
        self.assertEqual(set(calls), {'good', 'bad'})
        self.assertEqual(state['not_started'], ['third'])
        self.assertFalse(state['inventory_all_unsat'])

    def test_bounded_worker_pipeline_and_subset_scope(self):
        lock = threading.Lock(); live=0; high=0
        def worker(case):
            nonlocal live, high
            with lock: live+=1; high=max(high,live)
            time.sleep(.02)
            with lock: live-=1
            return {'id': case['id'], 'status': 'UNSAT_CROSSCHECKED'}
        state = {'results': []}
        d.dispatch([{'id': str(i)} for i in range(9)], worker, 3, self.root, state)
        self.assertLessEqual(high, 3); self.assertTrue(state['selected_all_unsat'])
        self.assertFalse(state['inventory_all_unsat']); self.assertEqual(len(state['results']),9)

    def test_h1_independent_historical_hash_check_and_basis(self):
        source=self.root/'manifest'; source.write_text('{}')
        cnf=self.root/'input.cnf'; cnf.write_text('p cnf 1 1\n1 0\n')
        digest=d.runner.sha256(cnf)
        case={'id':'h1_test','sector':'H1','cnf_sha256':None,'expected_historical_sha256':digest}
        plan={'config':{'generation_cap_seconds':120,'h1_generator_commit':'b'*40},
              'sources':{'H1':{'path':source,'sha256':'a'*64}}}
        def materialized(*args, **kwargs):
            return {'id':'h1_test','sector':'H1','cnf_path':str(cnf),'cnf_sha256':digest}
        with patch.object(d.h1,'materialize',side_effect=materialized):
            result=d.prepare(case,plan,self.root)
            self.assertEqual(result['identity_basis'],'historical')
            case['expected_historical_sha256']='0'*64
            with self.assertRaisesRegex(ValueError,'frozen historical identity'):d.prepare(case,plan,self.root)
            case['expected_historical_sha256']=None
            self.assertEqual(d.prepare(case,plan,self.root)['identity_basis'],'new')

    def test_load_exact_real_index_and_reject_hash_restore_race(self):
        base = Path(d.__file__).resolve().parent.parent
        config = {'schema': 'erdos85-dispatch-v1', 'not_before': '2026-09-11T07:00:00Z',
          'generation_cap_seconds':120, 'h1_generator_commit':'1a15845782e7b503d01393649948aa3ee5b007ba',
          'index': {'path':str(base/'phase_b_survivors_20260910.json'),
                    'sha256':d.runner.sha256(base/'phase_b_survivors_20260910.json')},
          'tool_sha256':{n:d.runner.sha256(base/'sat49'/n) for n in d.TOOLS},
          'policies':{s:{'crosscheck':s!='H1','primary_cap_seconds':1800,'crosscheck_cap_seconds':1800} for s in d.COUNTS}}
        path = self.root/'config.json'; path.write_text(json.dumps(config))
        plan = d.load_plan(path)
        self.assertEqual(len(plan['cases']),1416); d.check_sources(plan)
        self.assertEqual(sum(c['expected_historical_sha256'] is not None for c in plan['cases']),1066)
        config['crosscheck_ids']=['h1_003597af8a184e9f']; path.write_text(json.dumps(config))
        overridden=d.load_plan(path)
        self.assertTrue(next(c for c in overridden['cases'] if c['id']=='h1_003597af8a184e9f')['policy']['crosscheck'])
        config['crosscheck_ids']=['missing']; path.write_text(json.dumps(config))
        with self.assertRaisesRegex(ValueError,'Unknown crosscheck ID'): d.load_plan(path)
        config.pop('crosscheck_ids')
        path.write_bytes(plan['raw'])
        path.write_text('{}')
        with self.assertRaisesRegex(ValueError,'dependency changed'): d.check_sources(plan)
        path.write_bytes(plan['raw']); d.check_sources(plan)
        # The captured bytes, not any subsequent reread, remain the plan identity.
        self.assertEqual(hashlib.sha256(plan['raw']).hexdigest(), d.runner.sha256(path))
        config['index']['sha256']='0'*64; path.write_text(json.dumps(config))
        with self.assertRaisesRegex(ValueError,'Pinned bytes changed'): d.load_plan(path)


if __name__ == '__main__': unittest.main()
