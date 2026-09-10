import copy
import hashlib
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
import plan_replay_shards as target
from capacity_queue import table_serialization_tag
from replay_common import ReplayError, canonical_json

class ShardPlanTests(unittest.TestCase):
    def setUp(self):
        self.jobs = []
        for i in range(4):
            table = json.dumps([[[0, 2], i + 1]])
            tag = table_serialization_tag(table)
            self.jobs.append({'tag': tag, 'profile': 0, 'local_index': i,
                'certificate_key': f'sat49/campaign-20260825/h1/{tag}.compact.lrat.gz',
                'certificate_gzip_sha256': 'a'*64, 'compact_lrat_sha256': 'b'*64,
                'cnf_sha256': 'c'*64, 'table_serialization': table,
                'table_sha256': hashlib.sha256(table.encode()).hexdigest()})
        self.jobs.sort(key=lambda j: j['tag'])
        self.raw = b''.join(canonical_json(j) for j in self.jobs)
        self.weights = {'schema': target.WEIGHTS_SCHEMA, 'unit': 'raw_bytes',
            'source': 'synthetic scheduling test; not real certificates',
            'weights': {j['tag']: w for j, w in zip(self.jobs, [9, 8, 7, 6])}}
        self.prefix = target.BASE_PREFIX + 'test/'
    def build(self):
        return target.partition(self.raw, canonical_json(self.weights), 2, self.prefix)
    def test_deterministic_balanced_exact_partition(self):
        plan, queues = self.build()
        self.assertEqual((plan, queues), self.build())
        self.assertEqual([r['weight'] for r in plan['shards']], [15, 15])
        self.assertEqual([r['jobs'] for r in plan['shards']], [2, 2])
        self.assertFalse(plan['launch_ready'])
        self.assertEqual(sorted(j['local_index'] for q in queues for j in target.read_queue(q)), list(range(4)))
        self.assertEqual({j['tag'] for j in target.read_queue(queues[0])}, {self.jobs[0]['tag'], self.jobs[3]['tag']})
    def test_rejects_noncanonical_duplicate_and_wrong_table_parent(self):
        cases = [self.raw + canonical_json(self.jobs[-1]), self.raw.replace(b'\n', b'\n\n', 1)]
        duplicate = copy.deepcopy(self.jobs); duplicate[1]['local_index'] = duplicate[0]['local_index']
        cases.append(b''.join(canonical_json(j) for j in duplicate))
        wrong = copy.deepcopy(self.jobs)
        wrong[0]['table_serialization'] = wrong[1]['table_serialization']; wrong[0]['table_sha256'] = wrong[1]['table_sha256']
        cases.append(b''.join(canonical_json(j) for j in wrong))
        for raw in cases:
            with self.subTest(raw=raw[:40]), self.assertRaises(ReplayError):
                target.partition(raw, canonical_json(self.weights), 2, self.prefix)
    def test_rejects_missing_extra_and_invalid_weights(self):
        for kind in ('missing', 'extra', 'zero', 'bool', 'float'):
            w = copy.deepcopy(self.weights); tag = self.jobs[0]['tag']
            if kind == 'missing': del w['weights'][tag]
            elif kind == 'extra': w['weights']['0'*16] = 1
            else: w['weights'][tag] = {'zero': 0, 'bool': True, 'float': 1.5}[kind]
            with self.subTest(kind=kind), self.assertRaises(ReplayError):
                target.partition(self.raw, canonical_json(w), 2, self.prefix)
    def test_rejects_invalid_shards_and_prefix(self):
        for n in (0, -1, 5, True):
            with self.subTest(n=n), self.assertRaises(ReplayError):
                target.partition(self.raw, canonical_json(self.weights), n, self.prefix)
        for prefix in (self.prefix+'../', self.prefix+'more/', '/', target.BASE_PREFIX, self.prefix+'//'):
            with self.subTest(prefix=prefix), self.assertRaises(ReplayError):
                target.partition(self.raw, canonical_json(self.weights), 2, prefix)
    def test_rejects_child_changes_even_with_recomputed_child_metadata(self):
        for kind in ('duplicate', 'omit', 'alter'):
            plan, queues = self.build()
            if kind == 'duplicate': queues[1] = queues[0]
            else:
                jobs = target.read_queue(queues[1])
                if kind == 'omit': jobs.pop()
                else: jobs[0]['cnf_sha256'] = 'd'*64
                queues[1] = b''.join(canonical_json(j) for j in jobs)
            child = target.read_queue(queues[1])
            plan['shards'][1].update(queue_sha256=target.digest(queues[1]), jobs=len(child),
                weight=sum(self.weights['weights'][j['tag']] for j in child))
            with self.subTest(kind=kind), self.assertRaises(ReplayError):
                target.verify_partition(self.raw, canonical_json(self.weights), plan, queues)
    def test_cli_capacity_binding_and_create_only(self):
        with tempfile.TemporaryDirectory() as tmp:
            r = Path(tmp); (r/'queue').write_bytes(self.raw); (r/'weights').write_bytes(canonical_json(self.weights))
            capacity = ('orbit\tprofile\tlocalIndex\n' + ''.join(f"{j['tag']}\tBBBB\t{j['local_index']}\n" for j in self.jobs)).encode()
            excluded_tag = table_serialization_tag(json.dumps([[[0, 2], 5]]))
            capacity += f'{excluded_tag}\tBBBB\t4\n'.encode()
            (r/'capacity').write_bytes(capacity)
            (r/'reindex').write_bytes(canonical_json({'schema': 'erdos85-h1-v2-capacity-reindex-v1',
                'inventory_sha256': 'e'*64, 'output_sha256': target.digest(capacity),
                'emitted_rows': 5, 'dropped_outside_capacity_tags': []}))
            argv = [sys.executable, str(Path(target.__file__)), '--queue', str(r/'queue'), '--weights', str(r/'weights'),
                '--capacity-index', str(r/'capacity'), '--reindex-receipt', str(r/'reindex'), '--inventory-sha256', 'e'*64,
                '--shards', '2', '--prefix', self.prefix, '--output-dir', str(r/'output')]
            result = subprocess.run(argv, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout+result.stderr)
            original = (r/'output/plan.json').read_bytes()
            inputs = json.loads((r/'output/inputs.json').read_bytes())
            self.assertEqual(inputs['capacity_rows'], 5)
            self.assertEqual(inputs['canonical_capacity_rows'], 13351)
            self.assertIsNone(inputs['accepted_set_sha256'])
            self.assertEqual(inputs['excluded_capacity_rows'], 1)
            excluded = json.loads((r/'output/excluded-capacity.json').read_bytes())
            self.assertEqual(excluded, [{'tag': excluded_tag, 'profile': 0, 'local_index': 4, 'status': 'UNRESOLVED'}])
            self.assertEqual(subprocess.run(argv, capture_output=True).returncode, 2)
            self.assertEqual((r/'output/plan.json').read_bytes(), original)
            argv[-1] = str(r/'bad-output'); (r/'capacity').write_bytes(capacity+b'corruption')
            self.assertEqual(subprocess.run(argv, capture_output=True).returncode, 2)
            self.assertFalse((r/'bad-output').exists())

if __name__ == '__main__': unittest.main()
