import copy
import hashlib
import json
import tempfile
import unittest
from pathlib import Path

import build_replay_manifest as target
from build_replay_queue import build
from replay_common import ReplayError, canonical_json
import test_build_replay_queue as queue_tests


class ShardFreezeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.inventory, cls.capacity, cls.terminals = queue_tests.BuildReplayQueueTests().inputs()

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.inventory_sha = hashlib.sha256(self.inventory).hexdigest()
        self.cert = self.select(self.capacity)
        self.terminal = self.select(self.terminals)
        self.queue, self.receipt = build(self.inventory, self.cert, self.terminal, False)
        for name, value in [('inventory', self.inventory), ('capacity', self.capacity),
                            ('cert', self.cert), ('terminal', self.terminal),
                            ('queue', self.queue)]:
            (self.root / name).write_bytes(value)

    @staticmethod
    def select(value):
        rows = value.splitlines()
        return b'\n'.join(rows[i] for i in [0, 2, 4, 1487, 5104]) + b'\n'

    def validate(self, receipt=None, complete=False):
        target.validate_shard_queue_inputs(
            inventory=self.root/'inventory', certificate_index=self.root/'cert',
            capacity_index=self.root/'capacity', terminal_index=self.root/'terminal',
            queue=self.root/'queue', receipt=self.receipt if receipt is None else receipt,
            inventory_sha256=self.inventory_sha, require_complete=complete)

    def test_preserves_global_ordinals_and_binds_distinct_index(self):
        self.validate()
        jobs = [json.loads(line) for line in self.queue.splitlines()]
        self.assertEqual(sorted((j['profile'], j['local_index']) for j in jobs),
                         [(0, 1), (0, 3), (1, 1), (2, 1)])
        args = (self.receipt, self.root/'queue', self.root/'capacity',
                self.root/'terminal', self.inventory_sha, 4, False)
        target.validate_queue_build_receipt(*args, certificate_index=self.root/'cert')
        with self.assertRaises(ReplayError):
            target.validate_queue_build_receipt(*args)
        with self.assertRaises(ReplayError):
            self.validate(complete=True)

    def test_rejects_forged_queue_even_with_rehashed_receipt(self):
        jobs = [json.loads(line) for line in self.queue.splitlines()]
        jobs[0]['cnf_sha256'] = 'd' * 64
        forged = b''.join(canonical_json(job) for job in jobs)
        (self.root/'queue').write_bytes(forged)
        receipt = copy.deepcopy(self.receipt)
        receipt['output_sha256'] = hashlib.sha256(forged).hexdigest()
        with self.assertRaisesRegex(ReplayError, 'independent reconstruction'):
            self.validate(receipt)

    def test_rejects_rehashed_altered_subset_rows(self):
        lines = self.cert.splitlines()
        fields = lines[1].split(b'\t')
        fields[-1] = b'd'*64
        lines[1] = b'\t'.join(fields)
        altered = b'\n'.join(lines) + b'\n'
        queue, receipt = build(self.inventory, altered, self.terminal, False)
        (self.root/'cert').write_bytes(altered)
        (self.root/'queue').write_bytes(queue)
        with self.assertRaisesRegex(ReplayError, 'exact capacity subset'):
            self.validate(receipt)

    def test_rejects_inventory_terminal_and_receipt_drift(self):
        for name in ('inventory', 'terminal'):
            path = self.root/name
            original = path.read_bytes()
            path.write_bytes(original + b'\n')
            with self.subTest(name=name), self.assertRaises(ReplayError):
                self.validate()
            path.write_bytes(original)
        receipt = dict(self.receipt, emitted_jobs=5)
        with self.assertRaises(ReplayError):
            self.validate(receipt)


if __name__ == '__main__':
    unittest.main()
