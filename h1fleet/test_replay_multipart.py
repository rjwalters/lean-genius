"""End-to-end mocked AWS adapter checks; no AWS binary or service is invoked."""
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

from replay_common import AwsCliObjectStore, ReplayError
from test_s3_multipart import FakeS3


class StoreS3(FakeS3):
    def __init__(self):
        super().__init__()
        self.remote = None
        self.gets = 0
        self.corrupt_get = False
        self.corrupt_metadata = False

    def __call__(self, argv, **kwargs):
        op = argv[2]
        def response(data, stderr=''):
            return subprocess.CompletedProcess(argv, 0, json.dumps(data), stderr)
        if op == 'head-object':
            if self.remote is None:
                return subprocess.CompletedProcess(argv, 1, '', '404 NoSuchKey')
            metadata = dict(self.metadata)
            if self.corrupt_metadata: metadata['unexpected'] = 'value'
            return response({'ContentLength': len(self.remote), 'ETag': '"complete"',
                             'LastModified': 'now', 'VersionId': 'v1', 'Metadata': metadata})
        if op == 'get-object-tagging':
            return response({'TagSet': []}, 'x-amz-request-id: mock-request')
        if op == 'get-object':
            self.gets += 1
            target = Path(argv[argv.index('--version-id') + 2])
            target.write_bytes(b'!' * len(self.remote) if self.corrupt_get else self.remote)
            return response({})
        result = super().__call__(argv, **kwargs)
        if op == 'complete-multipart-upload' and result.returncode == 0 and not self.embedded_error:
            self.remote = b''.join(self.uploaded)
        return result


class ReplayMultipartTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(); self.addCleanup(self.tmp.cleanup)
        self.source = Path(self.tmp.name) / 'object'; self.source.write_bytes(b'payload')
        self.fake = StoreS3(); self.store = AwsCliObjectStore('bucket', 'fake-aws')
        self.addCleanup(patch.stopall)
        patch('replay_common.SINGLE_PUT_LIMIT', 1).start()
        patch('replay_common.subprocess.run', side_effect=self.fake).start()

    def publish(self): return self.store.put_immutable('object', self.source, {'tag': 't'})

    def test_success_requires_full_readback(self):
        result = self.publish()
        self.assertEqual(result.sha256, hashlib.sha256(b'payload').hexdigest())
        self.assertEqual(self.fake.gets, 1)
        self.assertNotIn('put-object', [op for op, _ in self.fake.calls])

    def test_same_size_corrupt_get_rejected(self):
        self.fake.corrupt_get = True
        with self.assertRaisesRegex(ReplayError, 'GET read-back mismatch'): self.publish()

    def test_metadata_drift_rejected(self):
        self.fake.corrupt_metadata = True
        with self.assertRaisesRegex(ReplayError, 'immutable S3 collision'): self.publish()

    def test_existing_identical_object_verified_without_upload(self):
        self.publish(); self.fake.calls.clear()
        self.publish()
        self.assertEqual(self.fake.calls, [])
        self.assertEqual(self.fake.gets, 2)

    def test_existing_different_object_rejected(self):
        self.publish(); self.fake.remote = b'different'
        self.fake.metadata['sha256'] = hashlib.sha256(self.fake.remote).hexdigest()
        with self.assertRaisesRegex(ReplayError, 'immutable S3 collision'): self.publish()

    def test_failed_completion_not_hidden_then_explicit_retry_checks_winner(self):
        self.fake.fail = 'complete-multipart-upload'
        with self.assertRaisesRegex(ReplayError, 'multipart publication failed'): self.publish()
        self.assertEqual(self.fake.gets, 0)
        self.assertEqual(self.fake.calls[-1][0], 'abort-multipart-upload')
        self.fake.remote = b'payload'
        self.fake.fail = None
        self.fake.calls.clear()
        self.publish()
        self.assertEqual(self.fake.calls, [])
        self.assertEqual(self.fake.gets, 1)


if __name__ == '__main__': unittest.main()
