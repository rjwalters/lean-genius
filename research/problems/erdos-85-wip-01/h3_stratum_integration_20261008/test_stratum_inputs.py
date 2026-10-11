"""Check complete imported-object coverage with synthetic triple receipts only."""
import copy,json,unittest
from pathlib import Path
from stratum_inputs import object_ledger
from fixture_cell import complete_cell_fixture
ROOT=Path(__file__).resolve().parent
class LedgerChecks(unittest.TestCase):
    def setUp(self):
        self.spec,self.triple=complete_cell_fixture()
        self.pair=json.loads((ROOT.parent/'h3_pair_completion_review_20261008/AUDIT.json').read_text())
        self.runtime=json.loads((ROOT.parent/'h3_phase3_runtime_20261008/build-evidence/AUDIT.json').read_text())
    def result(self):return object_ledger(self.spec,self.pair,self.runtime,self.triple)
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
    def test_changed_cell_runtime(self):
        self.triple['imported_objects'][self.runtime['results'][0]['module']]['sha256']='wrong'
        with self.assertRaises(ValueError):self.result()
    def test_unaccepted_triple(self):
        self.triple['status']='PARTIAL_CAMPAIGN_ARTIFACT_AUDIT'
        with self.assertRaises(ValueError):self.result()
if __name__=='__main__':unittest.main()
