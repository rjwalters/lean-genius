"""Worker metadata gates only: no Lean, Docker, subprocesses or native searches."""
import copy
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import common
import worker


class WorkerMetadata(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.manifest = worker.read(common.PACKAGE / 'MANIFEST.json')
        self.case = next(c for c in self.manifest['cases'] if c['state'] == 'PENDING')
        self.limits = {'memory_bytes': 16 * 1024**3, 'cpu_quota_us': 200000,
                       'cpu_period_us': 100000, 'wall_seconds': 7200}
        self.launch = {'schema': 'erdos85-h3-triple-launch-v1', 'attempt_id': 'synthetic-attempt-0001',
            'case_id': self.case['id'], 'execution_commit': 'a' * 40, 'image_id': 'sha256:' + 'b' * 64,
            'instance_id': 'synthetic', 'slot': 'synthetic',
            'recorded_root': '/workspace/attempts/synthetic-attempt-0001', 'limits': self.limits,
            'code_sha256': {name: worker.digest(common.PACKAGE / name) for name in worker.CODE}}

    def test_valid_launch_metadata(self):
        self.assertEqual(worker.validate_launch(self.launch, self.manifest), self.case)

    def test_unbounded_and_oversized_limits_rejected(self):
        for key, value in [('memory_bytes', 17*1024**3), ('cpu_quota_us', 200001),
                           ('cpu_period_us', 0), ('wall_seconds', 7201), ('wall_seconds', True),
                           ('wall_seconds', -1), ('wall_seconds', float('inf'))]:
            with self.subTest(key=key, value=value):
                launch = copy.deepcopy(self.launch)
                launch['limits'][key] = value
                with self.assertRaises(ValueError):
                    worker.validate_launch(launch, self.manifest)

    def test_wrong_or_missing_launch_identity_rejected(self):
        for key, value in [('attempt_id', '../escape'), ('execution_commit', 'main'),
                           ('image_id', 'latest'), ('instance_id', ''), ('slot', ''),
                           ('recorded_root', '/tmp/synthetic-attempt-0001'),
                           ('recorded_root', '/workspace/../synthetic-attempt-0001'),
                           ('case_id', 'unknown'), ('code_sha256', {})]:
            with self.subTest(key=key):
                launch = copy.deepcopy(self.launch)
                launch[key] = value
                with self.assertRaises(ValueError):
                    worker.validate_launch(launch, self.manifest)

    def test_prior_credit_and_changed_source_rejected(self):
        launch = copy.deepcopy(self.launch)
        launch['case_id'] = next(c['id'] for c in self.manifest['cases'] if c['state'] == 'REUSED_PASS')
        with self.assertRaises(ValueError):
            worker.validate_launch(launch, self.manifest)
        launch = copy.deepcopy(self.launch)
        launch['code_sha256']['worker.py'] = '0' * 64
        with self.assertRaises(ValueError):
            worker.validate_launch(launch, self.manifest)

    def test_actual_cgroup_limits(self):
        (self.root / 'memory.max').write_text(str(self.limits['memory_bytes']))
        (self.root / 'memory.swap.max').write_text('0')
        (self.root / 'cpu.max').write_text('200000 100000')
        actual = worker.actual_limits(self.root)
        worker.check_limits(self.limits, actual)
        actual['cpu_quota_us'] = 1600000
        with self.assertRaises(ValueError):
            worker.check_limits(self.limits, actual)
        for name, bad, old in [('cpu.max', 'max 100000', '200000 100000'),
                               ('memory.max', 'max', str(self.limits['memory_bytes'])),
                               ('memory.swap.max', 'max', '0')]:
            with self.subTest(name=name):
                (self.root / name).write_text(bad)
                with self.assertRaises(ValueError):
                    worker.actual_limits(self.root)
                (self.root / name).write_text(old)

    def test_inventory_detects_changes_extras_and_symlinks(self):
        library = self.root / 'library'
        library.mkdir()
        p = library / 'synthetic.olean'
        p.write_bytes(b'synthetic object')
        old = worker.inventory_files(library)
        p.write_bytes(b'changed')
        self.assertNotEqual(worker.inventory_files(library), old)
        p.unlink()
        p.symlink_to(self.root / 'outside')
        with self.assertRaises(ValueError):
            worker.inventory_files(library)
        p.unlink()
        with self.assertRaises(ValueError):
            worker.inventory_files(library)

    def test_atomic_checkpoint(self):
        p = self.root / 'RUN.json'
        worker.atomic_json(p, {'status': 'CERTIFICATE_RETAINED'})
        self.assertEqual(json.loads(p.read_text()), {'status': 'CERTIFICATE_RETAINED'})
        self.assertFalse(p.with_suffix('.json.tmp').exists())

    def test_branch_import_paths_do_not_depend_on_mapping_order(self):
        roots = {'full_base': '/base', 'full_final': '/final', 'library': '/unused'}
        self.assertEqual(worker.import_paths(roots, '/private', '/case', 'full', '/packages'),
                         '/private:/case:/final:/base:/packages')
        self.assertEqual(worker.import_paths({'deficient_base': '/def'}, '/private', '/case',
                                            'deficient', '/packages'),
                         '/private:/case:/def:/packages')

    def test_local_host_refusal_precedes_file_or_process_work(self):
        argv = ['worker.py', '--launch', '/missing', '--launch-sha256', 'x',
                '--cache-inventory', '/missing', '--stop-file', '/missing']
        with patch('sys.argv', argv), patch('worker.platform.system', return_value='Darwin'), \
                patch('worker.subprocess.Popen') as process:
            with self.assertRaisesRegex(ValueError, 'cloud Docker'):
                worker.main()
            process.assert_not_called()


if __name__ == '__main__':
    unittest.main(verbosity=2)
