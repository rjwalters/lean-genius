"""Frozen-input drift checks with synthetic sweep metadata; no search."""
import json,shutil,tempfile,unittest
from pathlib import Path
import test_prepare
from common import ROOT,REPO,sha,load_inputs
class InputChecks(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory();self.addCleanup(self.tmp.cleanup)
        self.repo=Path(self.tmp.name);self.root=self.repo/'plan';self.root.mkdir()
        fixture=test_prepare.PlanChecks();fixture.setUp();self.plan=fixture.plan()
        old=json.loads((ROOT.parent/'h3_native_sweep_20261008/PLAN.json').read_text())
        self.plan['inputs']=old['inputs'].copy()
        for name,entry in self.plan['inputs'].items():
            path=self.repo/entry['path'];path.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(REPO/entry['path'],path)
        for name,data in [('baseline',fixture.base),('sweep_audit',fixture.sweep)]:
            raw=json.dumps(data).encode();path=self.repo/(name+'.json');path.write_bytes(raw)
            self.plan['inputs'][name]={'path':path.name,'sha256':sha(raw)}
        self.plan['h5_observation_sha256']='0'*64;self.save()
    def save(self):(self.root/'PLAN.json').write_text(json.dumps(self.plan))
    def test_valid_pinned_inputs(self):self.assertEqual(load_inputs(self.root,self.repo)[0]['residual_residues'],[89,100,200])
    def test_mutated_input(self):
        (self.repo/'sweep_audit.json').write_text('{}')
        with self.assertRaises(ValueError):load_inputs(self.root,self.repo)
    def test_raised_cap(self):
        self.plan['limits']['per_part_seconds']=3600;self.save()
        with self.assertRaises(ValueError):load_inputs(self.root,self.repo)
    def test_raised_concurrency(self):
        self.plan['limits']['workers']=4;self.save()
        with self.assertRaises(ValueError):load_inputs(self.root,self.repo)
    def test_unaudited_object(self):
        self.plan['reused_parts'][0]['object_sha256']='1'*64;self.save()
        with self.assertRaises(ValueError):load_inputs(self.root,self.repo)
    def test_missing_residual(self):
        self.plan['residual_residues'].pop();self.save()
        with self.assertRaises(ValueError):load_inputs(self.root,self.repo)
    def test_added_residual(self):
        self.plan['residual_residues'].append(383);self.save()
        with self.assertRaises(ValueError):load_inputs(self.root,self.repo)
    def test_changed_authorization(self):
        self.plan['authorization']['room_message']=123;self.save()
        with self.assertRaises(ValueError):load_inputs(self.root,self.repo)
    def test_hidden_override(self):
        self.plan['retry_limit']=1;self.save()
        with self.assertRaises(ValueError):load_inputs(self.root,self.repo)
if __name__=='__main__':unittest.main()
