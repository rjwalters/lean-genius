"""Metadata mutations of the retained real probe; no Docker or Lean execution."""
import copy
from datetime import datetime, timedelta
import unittest

import audit_probe
import common
from validate_artifacts import read


class ProbeAudit(unittest.TestCase):
    def setUp(self):
        root = common.PACKAGE / 'container-probe-evidence'
        self.created, = read(root / 'created.json')
        self.terminal, = read(root / 'terminal.json')
        self.run = read(root / 'RUN.json')
        self.environment = read(root / 'container.stdout')
        # Relocate the metadata fixture to the current checkout for reading its
        # pinned toolchain/config files. Raw retained evidence is never edited.
        for obj in (self.created, self.terminal):
            for mount in obj['Mounts']:
                if mount['Destination'] == '/workspace':
                    mount['Source'] = str(common.REPO)

    def check(self):
        return audit_probe.validate(self.created, self.terminal, self.run,
                                    self.environment, common.REPO)

    def test_actual_probe_with_documented_default_normalization(self):
        self.assertIs(self.created['HostConfig']['OomKillDisable'], False)
        self.assertIsNone(self.terminal['HostConfig']['OomKillDisable'])
        result = self.check()
        self.assertEqual(result['container_exit'], 0)
        self.assertEqual(result['cpu_limit'], 2)
        self.assertTrue(result['read_only_inputs'])
        self.assertEqual(audit_probe.timestamp('2026-10-08T07:43:08.106298913Z').isoformat(),
                         '2026-10-08T07:43:08.106298+00:00')

    def test_wrong_image_or_identity(self):
        for field in ('Image', 'Id', 'Name'):
            with self.subTest(field=field):
                old = self.terminal[field]
                self.terminal[field] = 'wrong'
                with self.assertRaises(ValueError):
                    self.check()
                self.terminal[field] = old

    def test_limits_and_protection_changes(self):
        for key, value in [('Memory', 32 * 1024**3), ('MemorySwap', -1), ('CpuQuota', -1),
                           ('CpuPeriod', 200000), ('NanoCpus', 16000000000),
                           ('ReadonlyRootfs', False), ('NetworkMode', 'default'),
                           ('Privileged', True), ('OomKillDisable', True)]:
            with self.subTest(key=key):
                before = copy.deepcopy(self.created['HostConfig'])
                after = copy.deepcopy(self.terminal['HostConfig'])
                self.created['HostConfig'][key] = self.terminal['HostConfig'][key] = value
                with self.assertRaises(ValueError):
                    self.check()
                self.created['HostConfig'], self.terminal['HostConfig'] = before, after

    def test_writable_or_wrong_input_mount(self):
        for key, value in [('RW', True), ('Source', '/wrong')]:
            with self.subTest(key=key):
                before, after = copy.deepcopy(self.created['Mounts']), copy.deepcopy(self.terminal['Mounts'])
                for obj in (self.created, self.terminal):
                    mount = next(m for m in obj['Mounts'] if m['Type'] == 'bind')
                    mount[key] = value
                with self.assertRaises(ValueError):
                    self.check()
                self.created['Mounts'], self.terminal['Mounts'] = before, after

    def test_terminal_evidence_required_despite_pass_status(self):
        for key, value in [('Status', 'running'), ('Running', True), ('Pid', 42),
                           ('ExitCode', 1), ('OOMKilled', True)]:
            with self.subTest(key=key):
                old = self.terminal['State'][key]
                self.terminal['State'][key] = value
                with self.assertRaises(ValueError):
                    self.check()
                self.terminal['State'][key] = old

    def test_command_or_environment_changes(self):
        for key, value in [('Cmd', ['true']), ('Entrypoint', ['sh']), ('Env', ['LEAN_NUM_THREADS=1'])]:
            with self.subTest(key=key):
                before, after = copy.deepcopy(self.created['Config']), copy.deepcopy(self.terminal['Config'])
                self.created['Config'][key] = self.terminal['Config'][key] = value
                with self.assertRaises(ValueError):
                    self.check()
                self.created['Config'], self.terminal['Config'] = before, after

    def test_in_container_observation_and_source_pins(self):
        for key, value in [('limits', {'memory.max': 'max'}), ('toolchain', 'wrong'),
                           ('lake_manifest_sha256', '0' * 64), ('lean_version', 'Lean old'),
                           ('lean_path', '/unapproved')]:
            with self.subTest(key=key):
                old = self.environment[key]
                self.environment[key] = value
                with self.assertRaises(ValueError):
                    self.check()
                self.environment[key] = old

    def test_restart_and_wall_overrun(self):
        self.terminal['RestartCount'] = 1
        with self.assertRaises(ValueError):
            self.check()
        self.terminal['RestartCount'] = 0
        start = datetime.fromisoformat(self.terminal['State']['StartedAt'].replace('Z', '+00:00'))
        self.terminal['State']['FinishedAt'] = (start + timedelta(seconds=46)).isoformat()
        with self.assertRaises(ValueError):
            self.check()


if __name__ == '__main__':
    unittest.main(verbosity=2)
