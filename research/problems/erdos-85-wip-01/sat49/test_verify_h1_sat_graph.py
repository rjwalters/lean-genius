import itertools
from pathlib import Path
import tempfile
import unittest
from verify_h1_sat_graph import edge_prefix, verify_prefix, reconstruct, graph_stats, VerificationError, require_h1_graph, GraphDecodeError

class GraphTests(unittest.TestCase):
    def test_complete_injective_edge_map(self):
        previous=None
        for profile in range(5):
            ids, clauses=edge_prefix(profile)
            self.assertEqual(set(ids.values()),set(range(1,781)))
            self.assertEqual(set(ids),set(itertools.combinations(range(40),2)))
            if previous is not None:self.assertEqual(previous,ids)
            previous=ids
    def test_prefix_rejects_wrong_sign(self):
        with tempfile.TemporaryDirectory() as d:
            ids,clauses=edge_prefix(0);clauses[0]=[-clauses[0][0]]
            p=Path(d)/'input.cnf';p.write_text('p cnf 780 '+str(len(clauses))+'\n'+''.join(' '.join(map(str,c))+' 0\n' for c in clauses))
            with self.assertRaisesRegex(VerificationError,'prefix mismatch'):verify_prefix(p,0)
    def test_known_c4(self):
        r=graph_stats(4,[(0,1),(0,3),(1,2),(2,3)])
        self.assertFalse(r['c4_free']);self.assertEqual(r['maximum_common_neighbors'],2)
    def test_five_cycle(self):
        r=graph_stats(5,[(0,1),(0,4),(1,2),(2,3),(3,4)])
        self.assertTrue(r['c4_free']);self.assertEqual(r['minimum_degree'],2)
    def test_duplicate_edges_rejected(self):
        with self.assertRaisesRegex(VerificationError,'Duplicate'):graph_stats(2,[(0,1),(0,1)])
    def test_loop_rejected(self):
        with self.assertRaises(VerificationError):graph_stats(2,[(0,0)])
    def test_fixed_extension(self):
        ids,_=edge_prefix(0);edges=reconstruct([None]+[False]*780,ids);r=graph_stats(49,edges)
        self.assertEqual(r['degrees'],[1]*40+[7]*8+[8]);self.assertEqual(len(edges),52)
        self.assertTrue(r['c4_free'])
    def test_degree_deficient_graph_retains_diagnostics(self):
        ids,_=edge_prefix(0);edges=reconstruct([None]+[False]*780,ids)
        with self.assertRaises(GraphDecodeError) as caught:require_h1_graph(edges)
        self.assertEqual(caught.exception.evidence['status'],'GRAPH_DECODE_ERROR')
        self.assertEqual(caught.exception.evidence['edge_list'],edges)
        self.assertTrue(caught.exception.evidence['graph']['c4_free'])
        self.assertEqual(caught.exception.evidence['graph']['minimum_degree'],1)
    def test_missing_assignment(self):
        ids,_=edge_prefix(0)
        with self.assertRaisesRegex(VerificationError,'Missing'):reconstruct([None]+[False]*779,ids)

if __name__=='__main__':unittest.main()
