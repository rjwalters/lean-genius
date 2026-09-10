import hashlib
import json
from pathlib import Path
import sys
import tempfile
import time
import unittest
import materialize_h1_verdict_input as h

class InputTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
    def tearDown(self):
        self.tmp.cleanup()
    def inventory(self, **changes):
        table = [(h.PAIRS[0], 1)]
        tag = hashlib.sha1(json.dumps(table).encode()).hexdigest()[:16]
        row = dict(id='h1_' + tag, tag=tag, profile='2', table_values=[1]+[0]*23,
                   fleet_cnf_sha256='a'*64)
        row.update(changes)
        path = self.root/'inventory.json'
        path.write_text(json.dumps(dict(schema='erdos85-phase-b-h1-candidates-v1', rows=[row])))
        return path, h.sha256(path), row['id']
    def test_identity_and_table(self):
        row, table, expected = h.select_input(*self.inventory())
        self.assertEqual(json.loads(table), [[[0, 2], 1]])
        self.assertEqual(expected, 'a'*64)
    def test_tampered_inventory_rejected(self):
        path, digest, case = self.inventory()
        path.write_text(path.read_text()+' ')
        with self.assertRaisesRegex(ValueError, 'hash mismatch'):
            h.select_input(path, digest, case)
    def test_table_tag_mismatch(self):
        with self.assertRaisesRegex(ValueError, 'identity mismatch'):
            h.select_input(*self.inventory(table_values=[0]*24))
    def test_conflicting_historical_hashes(self):
        with self.assertRaisesRegex(ValueError, 'Conflicting'):
            h.select_input(*self.inventory(host_cnf_sha256='b'*64))
    def test_boolean_table_value_rejected(self):
        with self.assertRaisesRegex(ValueError, 'miss table'):
            h.select_input(*self.inventory(table_values=[True]+[0]*23))
    def run_child(self, script, limit=1000, timeout=2):
        return h.bounded_process([sys.executable, '-c', script], self.root/'out',
            self.root/'err', stdout_limit=limit, timeout=timeout)
    def test_capture_both_streams(self):
        r = self.run_child('import sys;print("ok");print("err",file=sys.stderr)')
        self.assertEqual(r['returncode'], 0)
        self.assertEqual((self.root/'out').read_text(), 'ok\n')
        self.assertEqual((self.root/'err').read_text(), 'err\n')
    def test_output_cap_not_written_past_bound(self):
        with self.assertRaisesRegex(ValueError, 'stdout exceeded'):
            self.run_child('import sys;sys.stdout.write("x"*10000)', limit=37)
        self.assertEqual((self.root/'out').stat().st_size, 37)
    def test_stderr_cap(self):
        with self.assertRaisesRegex(ValueError, 'stderr exceeded'):
            self.run_child('import sys;sys.stderr.write("x"*2000000)')
        self.assertEqual((self.root/'err').stat().st_size, 1024*1024)
    def test_timeout_terminates_child(self):
        started=time.monotonic()
        with self.assertRaises(TimeoutError):
            self.run_child('import time;time.sleep(30)', timeout=0.2)
        self.assertLess(time.monotonic()-started, 3)
    def test_cancellation_terminates_child(self):
        with self.assertRaises(InterruptedError):
            h.bounded_process([sys.executable, '-c', 'import time;time.sleep(30)'],
                self.root/'out', self.root/'err', stdout_limit=1000, timeout=2,
                cancelled=lambda: True)
    def test_never_overwrite_existing_output(self):
        (self.root/'out').write_text('retained')
        with self.assertRaises(FileExistsError):
            self.run_child('print("changed")')
        self.assertEqual((self.root/'out').read_text(), 'retained')

if __name__ == '__main__':
    unittest.main()
