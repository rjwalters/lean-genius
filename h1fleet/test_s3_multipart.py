import base64
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from urllib.parse import urlparse, unquote

from s3_multipart import conditional_multipart_upload, MultipartError, MIN_PART


class FakeS3:
    def __init__(self):
        self.calls = []
        self.uploaded = []
        self.fail = None
        self.bad_checksum = False
        self.embedded_error = False
        self.abort_failure = False
        self.mutate = None
        self.existing_object = b'winner bytes'

    def __call__(self, argv, **kwargs):
        op = argv[2]
        self.calls.append((op, list(argv)))
        def arg(name): return argv[argv.index(name) + 1]
        def reply(value): return subprocess.CompletedProcess(argv, 0, json.dumps(value), '')
        if self.fail == op or (op == 'abort-multipart-upload' and self.abort_failure):
            return subprocess.CompletedProcess(argv, 1, '', '412 PreconditionFailed')
        if op == 'create-multipart-upload':
            self.metadata = json.loads(arg('--metadata'))
            return reply({'UploadId': 'our-upload'})
        if op == 'upload-part':
            data = Path(arg('--body')).read_bytes()
            check = base64.b64encode(hashlib.sha256(data).digest()).decode()
            assert check == arg('--checksum-sha256')
            assert int(arg('--part-number')) == len(self.uploaded) + 1
            self.uploaded.append(data)
            if self.mutate: self.mutate()
            return reply({'ETag': f'"part-{len(self.uploaded)}"',
                          'ChecksumSHA256': 'bad' if self.bad_checksum else check})
        if op == 'complete-multipart-upload':
            assert arg('--if-none-match') == '*'
            assert arg('--upload-id') == 'our-upload'
            if self.embedded_error: return reply({'Error': {'Code': 'InternalError'}})
            manifest = json.loads(Path(unquote(urlparse(arg('--multipart-upload')).path)).read_text())
            parts = manifest['Parts']
            assert [p['PartNumber'] for p in parts] == list(range(1, len(parts) + 1))
            digests = b''.join(hashlib.sha256(x).digest() for x in self.uploaded)
            check = base64.b64encode(hashlib.sha256(digests).digest()).decode() + f'-{len(parts)}'
            return reply({'ETag': '"complete"', 'ChecksumSHA256': check})
        if op == 'abort-multipart-upload':
            assert arg('--upload-id') == 'our-upload'
            return reply({})
        raise AssertionError(op)


class MultipartTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.path = Path(self.tmp.name) / 'source'
        self.data = b'x' * MIN_PART + b'tail'
        self.path.write_bytes(self.data)
        self.fake = FakeS3()

    def upload(self, **changes):
        args = dict(aws='fake-aws', bucket='b', key='k', source=self.path,
                    metadata={'label': 'comma,equals=space value'},
                    expected_size=len(self.data), expected_sha256=hashlib.sha256(self.data).hexdigest(),
                    part_size=MIN_PART, runner=self.fake)
        args.update(changes)
        return conditional_multipart_upload(**args)

    def operations(self): return [op for op, _ in self.fake.calls]

    def test_success_streamed_parts_checksum_and_conditional_completion(self):
        result = self.upload()
        self.assertEqual(result['parts'], 2)
        self.assertEqual(b''.join(self.fake.uploaded), self.data)
        self.assertEqual(self.fake.metadata['label'], 'comma,equals=space value')
        self.assertNotIn('abort-multipart-upload', self.operations())

    def test_collision_never_overwrites_or_retries(self):
        self.fake.fail = 'complete-multipart-upload'
        with self.assertRaises(MultipartError): self.upload()
        self.assertEqual(self.fake.existing_object, b'winner bytes')
        self.assertEqual(self.operations().count('complete-multipart-upload'), 1)
        self.assertEqual(self.operations()[-1], 'abort-multipart-upload')

    def test_failed_part_aborts_without_completion(self):
        self.fake.fail = 'upload-part'
        with self.assertRaises(MultipartError): self.upload()
        self.assertNotIn('complete-multipart-upload', self.operations())
        self.assertEqual(self.operations()[-1], 'abort-multipart-upload')

    def test_bad_part_checksum_prevents_completion(self):
        self.fake.bad_checksum = True
        with self.assertRaisesRegex(MultipartError, 'part acknowledgement'): self.upload()
        self.assertNotIn('complete-multipart-upload', self.operations())

    def test_embedded_completion_error_fails(self):
        self.fake.embedded_error = True
        with self.assertRaisesRegex(MultipartError, 'error or malformed'): self.upload()
        self.assertEqual(self.operations()[-1], 'abort-multipart-upload')

    def test_abort_failure_is_visible(self):
        self.fake.fail = 'upload-part'; self.fake.abort_failure = True
        with self.assertRaisesRegex(MultipartError, 'abort failed for upload our-upload'): self.upload()

    def test_wrong_full_source_hash_never_completes(self):
        with self.assertRaisesRegex(MultipartError, 'source identity changed'):
            self.upload(expected_sha256='0' * 64)
        self.assertNotIn('complete-multipart-upload', self.operations())

    def test_source_replaced_mid_upload_fails(self):
        def mutate():
            other = self.path.with_suffix('.new'); other.write_bytes(self.data); other.replace(self.path)
        self.fake.mutate = mutate
        with self.assertRaisesRegex(MultipartError, 'source identity changed'): self.upload()
        self.assertNotIn('complete-multipart-upload', self.operations())

    def test_truncation_mid_upload_fails(self):
        self.fake.mutate = lambda: self.path.write_bytes(b'')
        with self.assertRaisesRegex(MultipartError, 'truncated'): self.upload()
        self.assertNotIn('complete-multipart-upload', self.operations())

    def test_invalid_inputs_never_start_upload(self):
        for changes in ({'part_size': 1}, {'expected_size': 0}, {'expected_size': MIN_PART * 10001},
                        {'metadata': {'sha256': 'wrong'}}, {'expected_sha256': 'BAD'}):
            with self.subTest(changes=changes), self.assertRaises(MultipartError): self.upload(**changes)
        self.assertEqual(self.fake.calls, [])

    def test_symlink_rejected(self):
        alias = self.path.with_suffix('.link'); alias.symlink_to(self.path)
        with self.assertRaises(MultipartError): self.upload(source=alias)
        self.assertEqual(self.fake.calls, [])

    def test_creation_failure_has_no_unknown_id_abort(self):
        self.fake.fail = 'create-multipart-upload'
        with self.assertRaises(MultipartError): self.upload()
        self.assertEqual(self.operations(), ['create-multipart-upload'])


if __name__ == '__main__': unittest.main()
