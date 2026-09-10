import hashlib
import itertools
from pathlib import Path
import tempfile
import subprocess
import sys
import unittest
from unittest import mock

import verify_small_high_sat_graph as v


class GraphDecoderTests(unittest.TestCase):
    def test_c4_free_positive_controls(self):
        for n in (3, 5, 7):
            edges = sorted({tuple(sorted((i, (i+1) % n))) for i in range(n)})
            _, result = v.graph_statistics(n, edges)
            self.assertEqual(result['degrees'], [2]*n)
            self.assertEqual(result['edges'], n)

    def test_actual_c4_and_duplicate_edges_rejected(self):
        with self.assertRaisesRegex(ValueError, 'C4 witnessed'):
            v.graph_statistics(4, [(0, 1), (1, 2), (2, 3), (0, 3)])
        with self.assertRaisesRegex(ValueError, 'duplicate'):
            v.graph_statistics(3, [(0, 1), (0, 1)])

    def test_edge_maps_are_complete_bijections(self):
        for h in (3, 5, 7):
            mapping = v.edge_variables(h)
            expected = set(itertools.combinations(range(h, 49), 2))
            self.assertEqual(set(mapping), expected)
            start = 1 if h == 7 else h*(h-1)//2+h*(49-h)+1
            self.assertEqual(set(mapping.values()), set(range(start, start+len(expected))))
        self.assertEqual(v.edge_variables(3)[(3, 4)], 142)
        self.assertEqual(v.edge_variables(5)[(5, 6)], 231)
        self.assertEqual(v.edge_variables(7)[(7, 8)], 1)

    def test_all_censuses_and_high_pair_intersections(self):
        expected = {(3, 0): [25, 18, 3, 0], (3, 1): [24, 21, 0, 1],
                    (5, 0): [14, 20, 10, 0], (5, 1): [13, 23, 7, 1],
                    (5, 2): [12, 26, 4, 2], (7, 0): [7, 14, 21, 0]}
        for (h, profile), census in expected.items():
            rows = v.supports(h, profile)
            self.assertEqual([sum(len(s) == k for s in rows.values()) for k in range(4)], census)
            for a in range(h):
                self.assertEqual(sum(a in s for s in rows.values()), 8)
            for a, b in itertools.combinations(range(h), 2):
                self.assertEqual(sum({a, b} <= s for s in rows.values()), 1)

    def test_invalid_profile_and_missing_edges_rejected(self):
        for h, profile in [(1, 0), (3, 2), (5, 3), (7, 1), (5, -1)]:
            with self.assertRaises(ValueError):
                v.supports(h, profile)
        with self.assertRaisesRegex(ValueError, 'Missing'):
            v.decode_and_check([False]*100, 5, 0)

    def test_satisfied_cnf_without_valid_graph_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            cnf, model = Path(tmp)/'input.cnf', Path(tmp)/'model.log'
            cnf.write_text('p cnf 29632 1\n-1 0\n')
            model.write_text('s SATISFIABLE\nv '+' '.join(str(-i) for i in range(1, 29633))+' 0\n')
            with self.assertRaisesRegex(v.GraphDecodeError, 'required49 vertex degrees') as caught:
                v.verify_candidate(cnf, model, 5, 0, hashlib.sha256(cnf.read_bytes()).hexdigest())
            evidence = caught.exception.evidence
            self.assertEqual(evidence['status'], 'GRAPH_REJECTED')
            self.assertEqual(evidence['cnf_sha256'], hashlib.sha256(cnf.read_bytes()).hexdigest())
            self.assertEqual(evidence['model_sha256'], hashlib.sha256(model.read_bytes()).hexdigest())
            self.assertEqual(evidence['graph']['order'], 49)
            self.assertEqual(evidence['graph']['edges'], 40)
            self.assertTrue(evidence['graph']['c4_free'])

    def test_huge_model_index_rejected_before_generic_allocation(self):
        with tempfile.TemporaryDirectory() as tmp:
            cnf, model = Path(tmp)/'input.cnf', Path(tmp)/'model.log'
            cnf.write_text('p cnf 29632 1\n-1 0\n')
            model.write_text('s SATISFIABLE\nv 999999999999999 0\n')
            with mock.patch.object(v.models, 'verify') as verify:
                with self.assertRaisesRegex(ValueError, 'Model variable exceeds'):
                    v.verify_candidate(cnf, model, 5, 0, 'a'*64)
                verify.assert_not_called()

    def test_cli_retains_rejected_graph_and_exits_nonzero(self):
        with tempfile.TemporaryDirectory() as tmp:
            cnf, model, output = (Path(tmp)/name for name in ('input.cnf', 'model.log', 'rejected.json'))
            cnf.write_text('p cnf 29632 1\n-1 0\n')
            model.write_text('s SATISFIABLE\nv '+' '.join(str(-i) for i in range(1, 29633))+' 0\n')
            run = subprocess.run([sys.executable, '-B', v.__file__, str(cnf), str(model),
                                  '--high-count', '5', '--profile', '0', '--cnf-sha256',
                                  hashlib.sha256(cnf.read_bytes()).hexdigest(), '--output', str(output)],
                                 capture_output=True, text=True, timeout=10)
            self.assertEqual(run.returncode, 1, run.stderr)
            evidence = v.json.loads(output.read_text())
            self.assertEqual(evidence['status'], 'GRAPH_REJECTED')
            self.assertEqual(len(evidence['graph']['edge_list']), 40)


if __name__ == '__main__':
    unittest.main()
