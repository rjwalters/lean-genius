import json
import unittest
from unittest.mock import patch

import check_retained_sat_candidate as checker
import test_check_retained_sat_candidate as original


class IndependentTests(unittest.TestCase):
    def setUp(self):
        self.f=original.HandoffTests('test_routes_bound_bytes')
        self.f.setUp()
        self.addCleanup(self.f.doCleanups)

    def test_different_model_report_from_decoder_rejected(self):
        graph=self.f.fake_graph()
        graph['model_sha256']='0'*64
        with patch.object(checker.h1,'verify_candidate',return_value=graph):
            with self.assertRaisesRegex(ValueError,'different input bytes'):
                self.f.check()

    def test_cnf_mutation_during_decoder_rejected(self):
        def decode(*args):
            self.f.cnf.write_text('p cnf 1 1\n-1 0\n')
            return self.f.fake_graph()
        with patch.object(checker.h1,'verify_candidate',side_effect=decode):
            with self.assertRaisesRegex(ValueError,'input changed'):
                self.f.check()

    def test_consistent_receipts_cannot_override_historical_source(self):
        source={'rows':[{'id':self.f.name,'profile':'0','historical_cnf_sha256':'f'*64}]}
        self.f.put(self.f.source,source)
        index=json.loads(self.f.index.read_text())
        source_sha=checker.file_hash(self.f.source)
        index['sources']['H1']['sha256']=source_sha
        self.f.put(self.f.index,index)
        self.f.ih=checker.file_hash(self.f.index)
        self.f.prep['manifest_sha256']=source_sha
        self.f.sync()
        with patch.object(checker.h1,'verify_candidate') as decode:
            with self.assertRaisesRegex(ValueError,'source identity'):
                self.f.check()
            decode.assert_not_called()

    def test_small_high_routing(self):
        # Only dispatch is mocked. This deliberately does not test a positive graph.
        for sector,profile,name,row in [
            ('H3',1,'h3_t1_canonical',{}),
            ('H5',2,'h5_t2.cube-0-0',{'cell':'h5_t2'}),
            ('H7',0,'cube_F6_t5',{}),
        ]:
            with self.subTest(sector=sector):
                f=original.HandoffTests('test_routes_bound_bytes')
                f.setUp()
                try:
                    solve=f.case/'solve'/name
                    f.solve.rename(solve)
                    log=solve/'kissat.log'
                    f.put(f.source,{'rows':[dict(row,id=name,cnf_sha256=f.expected)]})
                    sha=checker.file_hash(f.source)
                    f.put(f.index,{'sources':{sector:dict(path='source.json',sha256=sha,array='rows')},
                                  'cases':[dict(id=name,sector=sector,source_index=0,cnf_sha256=f.expected)]})
                    ih=checker.file_hash(f.index)
                    prep=dict(f.prep,id=name,sector=sector,manifest_sha256=sha)
                    solved=dict(f.solved,id=name,sector=sector)
                    f.put(f.case/'preparation.json',prep)
                    f.put(solve/'result.json',solved)
                    f.put(f.case/'result.json',dict(id=name,sector=sector,status='SAT_CANDIDATE',
                          index_sha256=ih,cnf_sha256=f.expected,preparation=prep,solve=solved))
                    graph=dict(status='GRAPH_WITNESS_VERIFIED',cnf_sha256=f.expected,
                               model_sha256=checker.file_hash(log))
                    with patch.object(checker.small,'verify_candidate',return_value=graph) as decode:
                        result=checker.check(f.case,f.index,ih,'kissat')
                        self.assertEqual(result['profile'],profile)
                        decode.assert_called_once_with(f.cnf,log,int(sector[1:]),profile,f.expected)
                finally:
                    f.doCleanups()


if __name__=='__main__':
    unittest.main()
