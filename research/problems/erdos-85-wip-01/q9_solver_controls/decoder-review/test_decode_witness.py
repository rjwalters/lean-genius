"""Offline checks only; no solver processes or experiment ledger mutations."""
import copy
import json
import tempfile
import unittest
from pathlib import Path
import decode_witness as w

ROOT = Path(__file__).resolve().parent


class DecoderChecks(unittest.TestCase):
    def test_existing_control_matches_independent_graph(self):
        graph, receipt = w.decode(ROOT / 'runs/000-N48-m24')
        independent = json.loads(Path('/Users/rwalters/lean-genius-q9-known-values-20260911/control48-review/graph.json').read_text())
        self.assertEqual({**graph, 'edges': len(graph['edges'])}, independent)
        self.assertEqual(receipt['degree_distribution'], {7: 48})
        self.assertEqual(receipt['edges'], 168)

    def fixture(self, path, mutation=None):
        meta = dict(schema=1, n=3, m=1, minimum_degree=2, vertex_label='block*m+residue',
                    variables=3, clauses=3, orbits=[dict(var=i+1, edges=[e]) for i, e in enumerate([[0,1],[0,2],[1,2]])])
        cnf = b'p cnf 3 3\n1 0\n2 0\n3 0\n'
        log = b's SATISFIABLE\nv 1 2 3 0\n'
        if mutation:
            meta, cnf, log = mutation(copy.deepcopy(meta), cnf, log)
        meta['cnf_sha256'] = w.digest(cnf)
        raw = (json.dumps(meta)+'\n').encode()
        result = dict(id=0, status='SAT', n=meta['n'], m=meta['m'], d=meta['minimum_degree'],
                      cnf={'sha256':w.digest(cnf)}, metadata={'sha256':w.digest(raw)}, output={'sha256':w.digest(log)})
        for name, data in [('input.cnf',cnf),('generator-metadata.json',raw),('solver.log',log),('result.json',json.dumps(result).encode())]:
            (path/name).write_bytes(data)

    def test_m1(self):
        with tempfile.TemporaryDirectory() as tmp:
            path=Path(tmp);self.fixture(path)
            graph, receipt=w.decode(path)
            self.assertEqual(graph['adjacency'],[[1,2],[0,2],[0,1]])
            self.assertEqual(receipt['degree_distribution'],{2:3})

    def test_bad_model_and_pin(self):
        with tempfile.TemporaryDirectory() as tmp:
            path=Path(tmp)
            for log in [b's SATISFIABLE\nv -1 2 3 0\n',b's SATISFIABLE\nv 1 2 0\n',b's SATISFIABLE\nv 1 -1 2 3 0\n']:
                self.fixture(path,lambda m,c,l:(m,c,log))
                with self.assertRaises(ValueError):w.decode(path)
            self.fixture(path)
            (path/'solver.log').write_text('s SATISFIABLE\nv -1 2 3 0\n')
            with self.assertRaisesRegex(ValueError,'pin mismatch'):w.decode(path)

    def test_invalid_map_and_degree(self):
        with tempfile.TemporaryDirectory() as tmp:
            path=Path(tmp)
            def duplicate(m,c,l):
                m['orbits'][1]['edges']=[[0,1]]
                return m,c,l
            def missing(m,c,l):
                m['orbits'].pop()
                return m,c,l
            def degree(m,c,l):
                m['minimum_degree']=3
                return m,c,l
            for mutation in [duplicate,missing,degree]:
                self.fixture(path,mutation)
                with self.assertRaises(ValueError):w.decode(path)

    def test_c4_rejected_even_with_satisfying_assignment(self):
        with tempfile.TemporaryDirectory() as tmp:
            path=Path(tmp)
            def cycle(m,c,l):
                m.update(n=4,variables=6,clauses=6,orbits=[dict(var=i+1,edges=[list(e)]) for i,e in enumerate([(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)])])
                return m,b'p cnf 6 6\n1 0\n-2 0\n3 0\n4 0\n-5 0\n6 0\n',b's SATISFIABLE\nv 1 -2 3 4 -5 6 0\n'
            self.fixture(path,cycle)
            with self.assertRaisesRegex(ValueError,'C4 found'):w.decode(path)


if __name__=='__main__':
    unittest.main(verbosity=2)
