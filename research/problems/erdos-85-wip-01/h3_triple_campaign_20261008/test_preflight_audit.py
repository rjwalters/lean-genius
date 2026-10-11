"""Mutate real retained Docker observations; never run Lean or Docker."""
import copy
from datetime import timedelta
from pathlib import Path
import unittest
from unittest.mock import patch

import audit_preflight as audit
import common
from validate_artifacts import read


class PreflightAudit(unittest.TestCase):
    def setUp(self):
        root = common.PACKAGE / 'worker-preflight-full-evidence'
        self.created, = read(root / 'created.json')
        self.terminal, = read(root / 'terminal.json')
        self.host, self.launch = read(root / 'HOST.json'), read(root / 'LAUNCH.json')
        self.repo = Path('/opt/e85/wt/erdos85__h3-triple-formal-20261007')
        self.output = self.repo / audit.RELATIVE / '_build/worker-preflight-full-first'

    def check(self):
        with patch.object(audit, 'digest', return_value=self.host['launch_sha256']):
            return audit.validate_container(self.created, self.terminal, self.host,
                                            self.launch, self.repo, self.output)

    def test_real_terminal_observations(self):
        self.assertGreater(self.check(), 0)
        self.assertLess(self.check(), 660)

    def test_resource_mutations(self):
        for key, value in [('Memory', 32 * 1024**3), ('MemorySwap', -1), ('CpuQuota', -1),
                           ('CpuPeriod', 200000), ('NanoCpus', 16000000000), ('PidsLimit', 512),
                           ('ReadonlyRootfs', False), ('NetworkMode', 'default'),
                           ('Privileged', True), ('OomKillDisable', True)]:
            with self.subTest(key=key):
                before, after = copy.deepcopy(self.created), copy.deepcopy(self.terminal)
                self.created['HostConfig'][key] = self.terminal['HostConfig'][key] = value
                with self.assertRaises(ValueError):
                    self.check()
                self.created, self.terminal = before, after

    def test_writable_inputs_or_extra_mount(self):
        for index in range(len(self.created['Mounts'])):
            with self.subTest(index=index):
                before, after = copy.deepcopy(self.created), copy.deepcopy(self.terminal)
                for obj in (self.created, self.terminal):
                    obj['Mounts'][index]['RW'] = not obj['Mounts'][index]['RW']
                with self.assertRaises(ValueError):
                    self.check()
                self.created, self.terminal = before, after
        for obj in (self.created, self.terminal):
            obj['Mounts'].append(copy.deepcopy(obj['Mounts'][0]))
        with self.assertRaises(ValueError):
            self.check()

    def test_terminal_failure_or_missing_state(self):
        for key, value in [('Status', 'running'), ('Running', True), ('Pid', 5),
                           ('ExitCode', 1), ('OOMKilled', True)]:
            with self.subTest(key=key):
                old = self.terminal['State'][key]
                self.terminal['State'][key] = value
                with self.assertRaises(ValueError):
                    self.check()
                self.terminal['State'][key] = old

    def test_command_environment_and_identity(self):
        for key, value in [('Cmd', ['true']), ('Entrypoint', ['sh']), ('Env', [])]:
            with self.subTest(key=key):
                before, after = copy.deepcopy(self.created), copy.deepcopy(self.terminal)
                self.created['Config'][key] = self.terminal['Config'][key] = value
                with self.assertRaises(ValueError):
                    self.check()
                self.created, self.terminal = before, after
        self.terminal['Id'] = 'different'
        with self.assertRaises(ValueError):
            self.check()

    def test_restart_or_wall_overrun(self):
        self.terminal['RestartCount'] = 1
        with self.assertRaises(ValueError):
            self.check()
        self.terminal['RestartCount'] = 0
        start = audit.timestamp(self.terminal['State']['StartedAt'])
        self.terminal['State']['FinishedAt'] = (start + timedelta(seconds=661)).isoformat()
        with self.assertRaises(ValueError):
            self.check()


if __name__ == '__main__':
    unittest.main(verbosity=2)
