"""Exercise the exact slot_loop AST with fake store/batch operations.

No import of campaign modules, AWS call, proof search, Docker or Lean execution.
The delayed first listing lets another slot reach claiming before either batch
starts, reproducing the original limit race. Proposed code must keep the limit
and release pending capacity on every pre-claim exit path.
"""
import ast
import hashlib
import json
from pathlib import Path
import threading
import time
from types import SimpleNamespace
import unittest

ROOT = Path(__file__).resolve().parent


def exercise(filename, mode='race', max_batches=1):
    path = ROOT / filename
    tree = ast.parse(path.read_text())
    function, = [n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name == 'slot_loop']
    state = {'errors': 0, 'done': 0, 'items': 0, 'stop': False, 'active': {}, 'statuses': {}}
    node_lock, store_lock = threading.Lock(), threading.Lock()
    second_listing = threading.Event()
    claims, batch_ids, logs, failures = set(), [], [], []

    class Store:
        listings = 0

        def exists(self, key):
            return mode == 'stop'

        def listing(self, prefix):
            if mode == 'store_error':
                raise RuntimeError('injected store error')
            with store_lock:
                self.listings += 1
                if self.listings >= 2:
                    second_listing.set()
            if mode == 'race':
                # The original admits both slots; the fixed version admits one,
                # which proceeds after this bounded simulated network delay.
                second_listing.wait(timeout=0.25)
            with store_lock:
                return set(claims)

        def put_new(self, key, marker):
            row_id = key.removeprefix('claims/')
            with store_lock:
                if row_id in claims:
                    return False
                claims.add(row_id)
                return True

    def batch(args, store, slot, row):
        if mode == 'batch_error':
            raise RuntimeError('injected batch error')
        with store_lock:
            batch_ids.append(row['id'])
        return {'id': row['id'], 'status': 'CERTIFIED', 'ran': 1, 'items': 1, 'certified': 1}

    namespace = {'node': state, 'lock': node_lock, 'STARTED': time.time(), 'MAX_NODE_ERRORS': 6,
                 'time': SimpleNamespace(time=time.time, sleep=lambda seconds: None),
                 'run_batch': batch, 'log': logs.append}
    exec(compile(ast.Module(body=[function], type_ignores=[]), str(path), 'exec'), namespace)
    args = SimpleNamespace(local_store=True, max_batches=max_batches, out=Path('/mock-only'),
                           lifetime=-1 if mode == 'expired' else 60, min_left=0)
    rows = [] if mode == 'empty' else [{'id': 'batch-a'}, {'id': 'batch-b'}]
    store = Store()

    def target(slot):
        try:
            namespace['slot_loop'](args, store, slot, rows)
        except BaseException as error:
            failures.append(repr(error))

    threads = [threading.Thread(target=target, args=(slot,), daemon=True) for slot in range(2)]
    for thread in threads:
        thread.start()
    for thread in threads:
        thread.join(timeout=3)
    if any(thread.is_alive() for thread in threads):
        raise AssertionError('Mock worker did not terminate')
    if failures:
        raise AssertionError(failures)
    return {'source_sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
            'mode': mode, 'limit': max_batches, 'claimed': sorted(claims),
            'completed': sorted(batch_ids), 'state': state, 'logs': logs}


class Reservation(unittest.TestCase):
    def test_original_overshoots_one_batch_limit(self):
        result = exercise('cert_worker.before.py')
        self.assertEqual(len(result['claimed']), 2)
        self.assertEqual(result['state']['done'], 2)

    def test_proposal_enforces_one_batch_limit(self):
        result = exercise('cert_worker.proposed.py')
        self.assertEqual(len(result['claimed']), 1)
        self.assertEqual(result['state']['done'], 1)
        self.assertEqual(result['state']['active'], {})

    def test_stop_expiry_empty_and_store_errors_release_capacity(self):
        for mode in ('stop', 'expired', 'empty', 'store_error'):
            with self.subTest(mode=mode):
                result = exercise('cert_worker.proposed.py', mode=mode)
                self.assertEqual(result['claimed'], [])
                self.assertEqual(result['state']['done'], 0)
                self.assertEqual(result['state']['active'], {})

    def test_batch_exception_releases_capacity(self):
        result = exercise('cert_worker.proposed.py', mode='batch_error')
        self.assertEqual(result['state']['active'], {})
        self.assertGreater(result['state']['errors'], 0)

    def test_unlimited_mode_still_runs_available_batches(self):
        result = exercise('cert_worker.proposed.py', mode='normal', max_batches=0)
        self.assertEqual(result['state']['done'], 2)
        self.assertEqual(result['state']['active'], {})


if __name__ == '__main__':
    suite = unittest.defaultTestLoader.loadTestsFromTestCase(Reservation)
    run = unittest.TextTestRunner(verbosity=2).run(suite)
    if not run.wasSuccessful():
        raise SystemExit(1)
    print(json.dumps({'status': 'MOCKED_CANARY_RACE_REPRODUCED_AND_PATCH_VALIDATED',
                      'original': exercise('cert_worker.before.py'),
                      'proposed': exercise('cert_worker.proposed.py'),
                      'tests_run': run.testsRun,
                      'scope': 'Exact slot_loop AST with mocked store and batch execution. '
                               'No AWS, solver, Lean, production canary or source integration.'}, indent=2))
