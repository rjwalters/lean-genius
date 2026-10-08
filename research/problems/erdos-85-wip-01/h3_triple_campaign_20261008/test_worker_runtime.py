"""Cloud-host-only child-process tests; no Lean or mathematical searches."""
import os
from pathlib import Path
import platform
import sys
import tempfile
import time
import unittest

import worker


class WorkerRuntime(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        if platform.system() != 'Linux' or not Path('/opt/e85/jobs').is_dir():
            raise RuntimeError('Run these process tests only on the existing cloud builder')

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)

    def run_child(self, source, seconds=5):
        return worker.bounded([sys.executable, '-c', source], self.root / 'child.log',
                              os.environ.copy(), time.monotonic() + seconds)

    def test_success_exit_log_and_usage(self):
        result = self.run_child('print("child completed", flush=True)')
        self.assertEqual(result['exit_code'], 0)
        self.assertFalse(result['deadline_exceeded'])
        self.assertEqual((self.root / 'child.log').read_text(), 'child completed\n')
        self.assertEqual(result['log_sha256'], worker.digest(self.root / 'child.log'))
        self.assertGreater(result['max_rss_kib'], 0)

    def test_nonzero_is_not_timeout(self):
        result = self.run_child('print("deliberate failure", flush=True); raise SystemExit(7)')
        self.assertEqual(result['exit_code'], 7)
        self.assertFalse(result['deadline_exceeded'])

    def test_timeout_kills_child_and_descendant(self):
        source = ('import subprocess,sys,time; '
                  'p=subprocess.Popen([sys.executable,"-c","import time; time.sleep(60)"]); '
                  'print(p.pid,flush=True); time.sleep(60)')
        result = self.run_child(source, seconds=1)
        self.assertTrue(result['deadline_exceeded'])
        self.assertEqual(result['exit_code'], -9)
        self.assertLess(result['elapsed_seconds'], 5)
        pid = int((self.root / 'child.log').read_text())
        # A killed orphan may briefly remain as a zombie before init reaps it.
        stat = Path('/proc') / str(pid) / 'stat'
        for _ in range(20):
            if not stat.exists() or stat.read_text().split(') ')[1].split()[0] == 'Z':
                break
            time.sleep(0.05)
        else:
            self.fail('Descendant remained alive after process-group timeout')

    def test_existing_log_refused_without_running_child(self):
        (self.root / 'child.log').write_text('retain')
        with self.assertRaises(FileExistsError):
            self.run_child('raise SystemExit(0)')
        self.assertEqual((self.root / 'child.log').read_text(), 'retain')


if __name__ == '__main__':
    unittest.main(verbosity=2)
