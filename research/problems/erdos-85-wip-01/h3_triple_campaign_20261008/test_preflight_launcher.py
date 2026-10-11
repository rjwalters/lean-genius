"""Launcher command and refusal tests, with no Docker/Lean/cloud execution."""
from pathlib import Path
import unittest
from unittest.mock import patch

import common
import launch_preflight as host
import worker


class PreflightLauncher(unittest.TestCase):
    def test_record_is_preflight_and_fresh(self):
        manifest = worker.read(common.PACKAGE / 'MANIFEST.json')
        case = next(c for c in manifest['cases'] if c['state'] == 'PENDING')
        output = host.REPO / 'research/problems/erdos-85-wip-01/h3_triple_campaign_20261008/_build/test'
        a = host.launch_record(case, output, 'm', 'c', '/pinned', 'a' * 40)
        b = host.launch_record(case, output, 'm', 'c', '/pinned', 'a' * 40)
        self.assertEqual(a['mode'], 'preflight')
        self.assertNotEqual(a['attempt_id'], b['attempt_id'])
        self.assertEqual(a['limits']['memory_bytes'], 16 * 1024**3)
        self.assertEqual(a['limits']['cpu_quota_us'], 200000)
        self.assertEqual(a['limits']['wall_seconds'], 600)
        self.assertEqual(Path(a['recorded_root']).name, a['attempt_id'])

    def test_exactly_one_writable_bind(self):
        with patch.object(host, 'REPO', common.REPO):
            output = common.PACKAGE / '_build/test'
            command = host.docker_command('test', output, '0' * 64)
        mounts = [command[i + 1] for i, word in enumerate(command) if word == '--mount']
        self.assertEqual(len(mounts), 4)
        writable = [m for m in mounts if not m.endswith(',readonly')]
        self.assertEqual(len(writable), 1)
        self.assertIn('source=' + str(output / 'work'), writable[0])
        self.assertIn('--read-only', command)
        self.assertEqual(command[command.index('--network') + 1], 'none')
        self.assertEqual(command[command.index('--cpu-quota') + 1], '200000')
        self.assertIn(host.probe_container.IMAGE, command)
        self.assertEqual(command[-2], '--stop-file')

    def test_local_host_refusal_precedes_subprocesses(self):
        args = ['launch_preflight.py', '--case', 'full-u001-r16',
                '--manifest-sha256', 'x', '--output', '/missing']
        with patch('sys.argv', args), patch('launch_preflight.platform.system', return_value='Darwin'), \
                patch('launch_preflight.subprocess.run') as run, \
                patch('launch_preflight.subprocess.check_output') as check:
            with self.assertRaisesRegex(ValueError, 'existing cloud builder'):
                host.main()
            run.assert_not_called()
            check.assert_not_called()


if __name__ == '__main__':
    unittest.main(verbosity=2)
