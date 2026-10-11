"""Small synthetic artifact tests; fixtures are NOT Lean compilation evidence."""
import copy
import json
from pathlib import Path
import tempfile
import unittest

import common
import validate_artifacts as audit


class Artifacts(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.manifest = common.PACKAGE / 'MANIFEST.json'
        self.manifest_sha = audit.digest(self.manifest)
        self.case = next(c for c in audit.read(self.manifest)['cases'] if c['state'] == 'PENDING')
        self.recorded_root = '/workspace/attempts/synthetic-test-0001'
        self.directory = self.root / self.case['id']
        self.directory.mkdir()
        self.run = {'schema': 'erdos85-h3-triple-receipt-v1', 'production_native_search': True,
                    'manifest_sha256': self.manifest_sha, 'case_id': self.case['id'],
                    'attempt_id': 'synthetic-test-0001', 'recorded_root': self.recorded_root,
                    'status': 'WORKER_REPORTED_SUCCESS_NOT_TRUSTED', 'results': []}
        for stage in audit.STAGES:
            name = self.case['module_prefix'] + stage
            (self.directory / (name + '.lean')).write_text(common.sources(self.case)[name + '.lean'])
            axioms = sorted(audit.STANDARD | ({self.case['namespace'] +
                '.rejected._native.native_decide.ax_1_1'} if stage != 'Membership' else set()))
            log = ''.join("'" + theorem + "' depends on axioms: [" + ', '.join(axioms) + ']\n'
                          for theorem in audit.exports(self.case, stage))
            (self.directory / (name + '.log')).write_text(log)
            (self.directory / (name + '.olean')).write_bytes(b'SYNTHETIC TEST OBJECT; NOT LEAN EVIDENCE')
            self.run['results'].append({'case_id': self.case['id'], 'module': name, 'stage': stage,
                'command': audit.command(self.case, stage, self.recorded_root), 'exit_code': 0,
                'elapsed_seconds': 1, 'user_cpu_seconds': 0.8, 'system_cpu_seconds': 0.2,
                'max_rss_kib': 100, 'axiom_exports': audit.reports(log)})
        self.save(rehash=True)

    def save(self, rehash=False):
        for e in self.run['results']:
            if rehash:
                for ext, key in (('.lean', 'source_sha256'), ('.log', 'log_sha256'), ('.olean', 'olean_sha256')):
                    e[key] = audit.digest(self.directory / (e['module'] + ext))
            (self.directory / (e['module'] + '.run.json')).write_text(json.dumps(e))
        (self.root / 'RUN.json').write_text(json.dumps(self.run))

    def check(self, certificate_only=False):
        return audit.validate_bundle(self.manifest, self.manifest_sha, self.case['id'],
                                     self.root, self.recorded_root, certificate_only)

    def test_complete_artifacts_do_not_credit_or_authorize_retry(self):
        result = self.check()
        self.assertEqual(result['status'], 'ARTIFACTS_VALID')
        self.assertFalse(result['campaign_credit'])
        self.assertFalse(result['retry_authorized'])

    def test_retained_certificate_survives_consumer_failure(self):
        self.run['results'][-1]['exit_code'] = 1
        self.run['status'] = 'ERROR'
        self.save()
        with self.assertRaises(ValueError):
            self.check()
        result = self.check(certificate_only=True)
        self.assertEqual(result['status'], 'CERTIFICATE_ARTIFACTS_VALID')
        self.assertEqual(len(result['results']), 3)
        self.assertFalse(result['retry_authorized'])

    def test_certificate_checkpoint_without_consumer(self):
        self.run['results'].pop()
        self.save()
        self.assertEqual(self.check(True)['status'], 'CERTIFICATE_ARTIFACTS_VALID')
        with self.assertRaises(ValueError):
            self.check()

    def test_partial_upload_or_no_certificate_never_passes(self):
        certificate = self.directory / (self.case['module_prefix'] + 'Certificate.olean')
        certificate.unlink()
        with self.assertRaises(ValueError):
            self.check(True)
        self.run['results'] = self.run['results'][:2]
        self.save()
        with self.assertRaises(ValueError):
            self.check(True)

    def test_every_retained_artifact_is_checked(self):
        for stage in audit.STAGES:
            for ext in ('.lean', '.log', '.olean', '.run.json'):
                with self.subTest(stage=stage, extension=ext):
                    path = self.directory / (self.case['module_prefix'] + stage + ext)
                    old = path.read_bytes()
                    path.write_bytes(old + b' ')
                    # JSON whitespace is semantically identical, so alter a field.
                    if ext == '.run.json':
                        path.write_text('{}')
                    with self.assertRaises((ValueError, KeyError)):
                        self.check()
                    path.write_bytes(old)

    def test_changed_source_even_with_updated_hash_rejected(self):
        name = self.case['module_prefix'] + 'Certificate.lean'
        p = self.directory / name
        p.write_text(p.read_text().replace('native_decide', 'sorry'))
        self.save(rehash=True)
        with self.assertRaisesRegex(ValueError, 'Changed generated source'):
            self.check()

    def test_raw_axioms_override_json_pass(self):
        e = self.run['results'][2]
        p = self.directory / (e['module'] + '.log')
        p.write_text(p.read_text().replace(self.case['namespace'] +
                     '.rejected._native.native_decide.ax_1_1', 'Other.rejected._native.native_decide.ax_1_1'))
        self.save(rehash=True)
        with self.assertRaisesRegex(ValueError, 'raw log'):
            self.check()
        e['axiom_exports'] = audit.reports(p.read_text())
        self.save()
        with self.assertRaisesRegex(ValueError, 'Wrong trust set'):
            self.check()

    def test_duplicate_extra_missing_exports_rejected(self):
        e = self.run['results'][2]
        p = self.directory / (e['module'] + '.log')
        old = p.read_text()
        for bad in ('', old + old, old + "'Other' does not depend on any axioms\n"):
            with self.subTest(log=bad):
                p.write_text(bad)
                self.save(rehash=True)
                with self.assertRaises(ValueError):
                    self.check()

    def test_malformed_reports_and_duplicate_axioms_rejected(self):
        for log in ("'x' depends on axioms: [propext", "'x' depends on axioms: [propext, propext]",
                    "'x' depends on axioms: [sorryAx]", 'source.lean:1:0: error: failed'):
            with self.subTest(log=log), self.assertRaises(ValueError):
                audit.reports(log)

    def test_bridge_and_wrong_receipt_bindings_rejected(self):
        original = copy.deepcopy(self.run)
        changes = [('schema', 'erdos85-h3-triple-bridge-canary-v1'),
                   ('production_native_search', False), ('manifest_sha256', '0' * 64),
                   ('case_id', 'full-u999-r99'), ('recorded_root', '/wrong'),
                   ('attempt_id', '../escape')]
        for key, value in changes:
            with self.subTest(key=key):
                self.run = copy.deepcopy(original)
                self.run[key] = value
                self.save()
                with self.assertRaises(ValueError):
                    self.check()

    def test_wrong_commands_metrics_stage_order_and_exit_rejected(self):
        original = copy.deepcopy(self.run)
        changes = [('command', ['true']), ('exit_code', False), ('exit_code', 1),
                   ('elapsed_seconds', float('nan')), ('max_rss_kib', -1),
                   ('certificate_substitution', True), ('case_id', 'other'),
                   ('module', 'Other'), ('stage', 'Inputs')]
        for key, value in changes:
            with self.subTest(key=key, value=value):
                self.run = copy.deepcopy(original)
                self.run['results'][2][key] = value
                self.save()
                with self.assertRaises(ValueError):
                    self.check()
        self.run = original
        self.run['results'][1:3] = reversed(self.run['results'][1:3])
        self.save()
        with self.assertRaises(ValueError):
            self.check()

    def test_empty_object_and_symlink_rejected(self):
        p = self.directory / (self.case['module_prefix'] + 'Certificate.olean')
        p.write_bytes(b'')
        self.save(rehash=True)
        with self.assertRaisesRegex(ValueError, 'Empty Lean object'):
            self.check()
        p.unlink()
        target = self.root / 'outside.olean'
        target.write_bytes(b'synthetic')
        p.symlink_to(target)
        self.save(rehash=True)
        with self.assertRaisesRegex(ValueError, 'linked artifact'):
            self.check()

    def test_duplicate_json_key_rejected(self):
        p = self.root / 'RUN.json'
        p.write_text('{"status":"PASS","status":"FAIL"}')
        with self.assertRaisesRegex(ValueError, 'Duplicate JSON key'):
            self.check()

    def test_reused_pilots_not_accepted_as_new_builds(self):
        credited = next(c for c in audit.read(self.manifest)['cases'] if c['state'] == 'REUSED_PASS')
        with self.assertRaisesRegex(ValueError, 'Prior credits'):
            audit.validate_bundle(self.manifest, self.manifest_sha, credited['id'],
                                  self.root, self.recorded_root)

    def test_real_bridge_canary_is_rejected(self):
        with self.assertRaises(ValueError):
            audit.validate_bundle(self.manifest, self.manifest_sha, self.case['id'],
                common.PACKAGE / 'canary-evidence', self.recorded_root)

    def test_preflight_is_never_a_rejection_receipt(self):
        self.run['schema'] = 'erdos85-h3-triple-preflight-v1'
        self.run['production_native_search'] = False
        self.run['results'] = self.run['results'][:2]
        self.save()
        result = audit.validate_bundle(self.manifest, self.manifest_sha, self.case['id'],
                                        self.root, self.recorded_root, preflight_only=True)
        self.assertEqual(result['status'], 'PREFLIGHT_ARTIFACTS_VALID')
        self.assertFalse(result['campaign_credit'])
        with self.assertRaises(ValueError):
            self.check()
        with self.assertRaises(ValueError):
            self.check(certificate_only=True)

    def test_production_cannot_be_reclassified_as_preflight(self):
        with self.assertRaises(ValueError):
            audit.validate_bundle(self.manifest, self.manifest_sha, self.case['id'],
                                  self.root, self.recorded_root, preflight_only=True)
        with self.assertRaises(ValueError):
            audit.validate_bundle(self.manifest, self.manifest_sha, self.case['id'],
                                  self.root, self.recorded_root, certificate_only=True,
                                  preflight_only=True)


if __name__ == '__main__':
    unittest.main(verbosity=2)
