"""Check complete imported-object coverage with synthetic triple receipts only."""
import copy,json,unittest
from pathlib import Path
from stratum_inputs import object_ledger
from transfer_pair import JOB
ROOT=Path(__file__).resolve().parent
class LedgerChecks(unittest.TestCase):
    def setUp(self):
        self.spec=json.loads((ROOT/'SOURCE.json').read_text())
        self.pair=json.loads((ROOT.parent/'h3_pair_completion_review_20261008/AUDIT.json').read_text())
        self.runtime=json.loads((ROOT.parent/'h3_phase3_runtime_20261008/build-evidence/AUDIT.json').read_text())
        self.sample=json.loads((ROOT.parent/'h3_native_parts_20261008/sample-evidence/AUDIT.json').read_text())
        reused=[x['residue'] for x in self.sample['accepted_parts']]
        self.triple={'status':'H3_TRIPLE_CELL_ARTIFACT_AUDIT_PASS','authoritative_exit':0,'job':JOB.name,
                     'execution_commit':self.spec['triple_source_commit'],'reused_residues':reused,
                     'accepted_new_residues':[r for r in range(384) if r not in reused],'accepted_parts':[]}
        for r in self.triple['accepted_new_residues']:
            module=f'Erdos85H3TripleCompletionPart{r:03d}'
            self.triple['accepted_parts'].append({'module':'Proofs.'+module,'source_sha256':self.spec['sources'][module]['source_sha256'],'object_sha256':'synthetic-only','object_bytes':1})
        module='Erdos85H3TripleCompletionCell'
        self.triple['cell']={'module':'Proofs.'+module,'source_sha256':self.spec['sources'][module]['source_sha256'],'object_sha256':'synthetic-cell-only','object_bytes':1}
    def result(self):return object_ledger(self.spec,self.pair,self.runtime,self.sample,self.triple)
    def test_complete_imports(self):self.assertEqual(len(self.result()),417)
    def test_missing_object(self):
        self.triple['accepted_parts'].pop()
        with self.assertRaises(ValueError):self.result()
    def test_duplicate_object(self):
        self.triple['accepted_parts'].append(copy.deepcopy(self.triple['accepted_parts'][0]))
        with self.assertRaises(ValueError):self.result()
    def test_wrong_source(self):
        self.triple['accepted_parts'][0]['source_sha256']='wrong'
        with self.assertRaises(ValueError):self.result()
    def test_empty_object(self):
        self.triple['accepted_parts'][0]['object_bytes']=0
        with self.assertRaises(ValueError):self.result()
    def test_missing_pair(self):
        self.pair['results'].pop()
        with self.assertRaises(ValueError):self.result()
    def test_missing_runtime(self):
        self.runtime['results'].pop()
        with self.assertRaises(ValueError):self.result()
    def test_unaccepted_sample(self):
        self.sample['status']='COMPILED_PENDING_AUDIT'
        with self.assertRaises(ValueError):self.result()
    def test_unaccepted_triple(self):
        self.triple['status']='PARTIAL_CAMPAIGN_ARTIFACT_AUDIT'
        with self.assertRaises(ValueError):self.result()
if __name__=='__main__':unittest.main()
