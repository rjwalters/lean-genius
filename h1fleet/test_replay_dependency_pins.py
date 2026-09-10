"""New execution dependency pins, with historical receipt compatibility."""
import json
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import test_replay_transaction as fixtures
from replay_common import ReplayError, canonical_json, load_manifest, sha256_file
from replay_worker import verify_multipart_dependency


class DependencyPinsTest(unittest.TestCase):
    def setUp(self):
        self.fixture = fixtures.ReplayTransactionTest()
        self.fixture.setUp()
        self.addCleanup(self.fixture.tearDown)

    def add_pins(self):
        f = self.fixture
        data = json.loads(f.manifest.read_text())
        data['s3_multipart_sha256'] = sha256_file(Path(__file__).with_name('s3_multipart.py'))
        data['queue_certificate_index_sha256'] = '1' * 64
        f.manifest.write_bytes(canonical_json(data))
        return data

    def test_historical_manifest_still_parses(self):
        f = self.fixture
        manifest = load_manifest(f.manifest)
        self.assertNotIn('s3_multipart_sha256', manifest)
        verify_multipart_dependency(manifest, production=False)
        with self.assertRaisesRegex(ReplayError, 'requires frozen'):
            verify_multipart_dependency(manifest, production=True)

    def test_optional_fields_reject_malformed_values(self):
        for field in ('s3_multipart_sha256', 'queue_certificate_index_sha256'):
            for value in (None, '', 'z' * 64, 123):
                with self.subTest(field=field, value=value):
                    data = self.add_pins()
                    data[field] = value
                    self.fixture.manifest.write_bytes(canonical_json(data))
                    with self.assertRaises(ReplayError):
                        load_manifest(self.fixture.manifest)

    def test_missing_or_changed_helper_rejected(self):
        manifest = self.add_pins()
        helper = self.fixture.root / 'missing.py'
        with self.assertRaisesRegex(ReplayError, 'cannot verify'):
            verify_multipart_dependency(manifest, production=True, helper=helper)
        helper.write_text('# modified helper\n')
        with self.assertRaisesRegex(ReplayError, 'differs from manifest'):
            verify_multipart_dependency(manifest, production=True, helper=helper)

    def test_wrong_pin_blocks_worker_before_consumption(self):
        data = self.add_pins()
        data['s3_multipart_sha256'] = '0' * 64
        f = self.fixture
        f.manifest.write_bytes(canonical_json(data))
        result = f.worker()
        self.assertEqual(result.returncode, 2)
        self.assertIn('dependency SHA-256 differs', result.stderr)
        self.assertNotEqual(f.store.head(f.certificate_key).tags.get('replay'), 'consumed')
        self.assertFalse(f.receipt_path().exists())

    def test_new_pins_survive_transaction_resume_and_validation(self):
        expected = self.add_pins()
        self.fixture.test_success_resume_and_independent_validation()
        receipt = json.loads(self.fixture.receipt_path().read_text())
        for key in ('s3_multipart_sha256', 'queue_certificate_index_sha256'):
            self.assertEqual(receipt['build_identity'][key], expected[key])

    def test_missing_pin_in_ready_is_rejected_on_resume(self):
        self.add_pins()
        f = self.fixture
        self.assertEqual(f.worker().returncode, 0)
        key = f'sat49/campaign-20260825/h1-replay/ready/{f.tag}.json'
        # An accepted transaction validates its bound ready record on resume.
        receipt = json.loads(f.receipt_path().read_text())
        key = receipt['replay_ready']['key']
        ready = json.loads((f.store.objects / key).read_text())
        del ready['build_identity']['s3_multipart_sha256']
        f.rewrite_store_json(key, ready)
        result = f.worker()
        self.assertEqual(result.returncode, 2)


if __name__ == '__main__':
    unittest.main()
