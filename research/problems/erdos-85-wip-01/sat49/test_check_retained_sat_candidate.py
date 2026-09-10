import copy
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import check_retained_sat_candidate as c


class HandoffTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.p = Path(self.tmp.name)
        self.case = self.p/'case'; self.case.mkdir()
        self.name = 'h1_test'; self.solve = self.case/'solve'/self.name; self.solve.mkdir(parents=True)
        self.cnf = self.case/'input.cnf'; self.cnf.write_text('p cnf 1 1\n1 0\n')
        self.log = self.solve/'kissat.log'; self.log.write_text('s SATISFIABLE\nv 1 0\n')
        self.expected = c.file_hash(self.cnf)
        self.source = self.p/'source.json'
        self.put(self.source, {'rows': [{'id': self.name, 'profile': '0'}]})
        sh = c.file_hash(self.source)
        self.index = self.p/'index.json'
        self.put(self.index, {'sources': {'H1': {'path': 'source.json', 'sha256': sh, 'array': 'rows'}},
                             'cases': [{'id': self.name, 'sector': 'H1', 'source_index': 0, 'cnf_sha256': None}]})
        self.ih = c.file_hash(self.index)
        self.prep = {'id': self.name, 'sector': 'H1', 'manifest_sha256': sh,
                     'cnf_path': str(self.cnf), 'cnf_sha256': self.expected}
        self.solved = {'id': self.name, 'sector': 'H1', 'cnf_sha256': self.expected, 'status': 'SAT_CANDIDATE',
                       'primary': {'verdict': 'SAT_CANDIDATE', 'returncode': 10, 'stop_reason': None,
                                   'log_bytes': self.log.stat().st_size, 'log_sha256': c.file_hash(self.log)}}
        self.sync()

    def put(self, p, d): p.write_text(json.dumps(d))
    def sync(self):
        self.put(self.case/'preparation.json', self.prep)
        self.put(self.solve/'result.json', self.solved)
        self.put(self.case/'result.json', dict(id=self.name, sector='H1', status=self.solved['status'],
                 index_sha256=self.ih, cnf_sha256=self.expected, preparation=self.prep, solve=self.solved))
    def check(self, solver='kissat'): return c.check(self.case, self.index, self.ih, solver)
    def fake_graph(self):
        return {'status': 'GRAPH_WITNESS_VERIFIED', 'cnf_sha256': self.expected,
                'model_sha256': c.file_hash(self.log)}

    def test_routes_bound_bytes(self):
        # This mock tests handoff only, not a positive 49-vertex graph.
        with patch.object(c.h1, 'verify_candidate', return_value=self.fake_graph()) as decoder:
            self.assertEqual(self.check()['status'], 'GRAPH_WITNESS_VERIFIED')
            decoder.assert_called_once_with(self.cnf, self.log, 0, self.expected)

    def test_log_tampering_rejected_before_decoder(self):
        self.log.write_text('s SATISFIABLE\nv -1 0\n')
        with patch.object(c.h1, 'verify_candidate') as decoder:
            with self.assertRaisesRegex(ValueError, 'log size/hash'): self.check()
            decoder.assert_not_called()

    def test_receipt_disagreement_rejected(self):
        bad = copy.deepcopy(self.prep); bad['cnf_sha256'] = '0'*64
        self.put(self.case/'preparation.json', bad)
        with self.assertRaisesRegex(ValueError, 'receipts disagree'): self.check()

    def test_mutation_during_decode_rejected(self):
        def fake(*args):
            self.source.write_text('{}')
            return self.fake_graph()
        with patch.object(c.h1, 'verify_candidate', side_effect=fake):
            with self.assertRaisesRegex(ValueError, 'changed during'): self.check()

    def test_disagreement_uses_cadical_sat_log(self):
        self.solved['status'] = 'DISAGREEMENT'
        self.solved['crosscheck'] = copy.deepcopy(self.solved['primary'])
        self.solved['primary']['verdict'] = 'UNSAT'
        (self.solve/'cadical.log').write_bytes(self.log.read_bytes()); self.sync()
        with patch.object(c.h1, 'verify_candidate', return_value=self.fake_graph()) as decoder:
            self.assertEqual(self.check('cadical')['original_solver_status'], 'DISAGREEMENT')
            self.assertEqual(decoder.call_args.args[1].name, 'cadical.log')
        with self.assertRaisesRegex(ValueError, 'did not return'): self.check()

    def test_graph_rejection_preserves_evidence(self):
        e = c.h1.GraphDecodeError('degree failure', {'status': 'GRAPH_DECODE_ERROR', 'edge_list': [[0,1]]})
        with patch.object(c.h1, 'verify_candidate', side_effect=e):
            r = self.check(); self.assertNotEqual(r['status'], 'GRAPH_WITNESS_VERIFIED')
            self.assertEqual(r['graph_check']['edge_list'], [[0,1]])

    def test_real_decoder_rejects_toy_encoding(self):
        with self.assertRaises(ValueError): self.check()

    def test_profiles_are_not_inferred_from_arbitrary_numbers(self):
        for sector, row, expected in [('H1', {'profile':'4'},4), ('H3', {'id':'h3_t1_canonical'},1),
                                      ('H5', {'cell':'h5_t2'},2), ('H7', {},0)]:
            self.assertEqual(c.select_profile(sector,row),expected)
        for sector,row in [('H1',{'profile':True}),('H3',{'id':'h3_t7_canonical'}),('H5',{'cell':'h5_t9'})]:
            with self.assertRaises(ValueError): c.select_profile(sector,row)


if __name__ == '__main__': unittest.main()
