"""Synthetic complete-sweep plan tests; never write a real PLAN or run Lean."""
import copy,json,unittest
from pathlib import Path
from prepare import build_plan,choose_workers,H5_JOB
ROOT=Path(__file__).resolve().parent
class PlanChecks(unittest.TestCase):
    def setUp(self):
        self.base=json.loads((ROOT.parent/'h3_native_campaign_20261008/ACCEPTANCE.json').read_text())
        self.manifest=json.loads((ROOT.parent/'h3_native_parts_20261008/MANIFEST.json').read_text())
        attempted=[r for r in range(384) if r not in self.base['accepted_unique_residues'] and r!=89]
        parts=[]
        for r in attempted:
            if r in (100,200):continue
            row=self.manifest['parts'][r]
            parts.append({'residue':r,'module':row['module'],'source_sha256':row['source_sha256'],'object_sha256':'0'*64,'object_bytes':1,
                          'axiom_exports':[{'theorem':row['theorem'],'axioms':['propext','Quot.sound',row['native_axiom']]}]})
        self.sweep={'status':'H3_SWEEP_ARTIFACT_AUDIT_PASS','authoritative_exit':0,'attempted_residues':attempted,'known_timeouts':[89],
                    'accepted_parts':parts,'accepted_new_residues':[p['residue'] for p in parts],
                    'new_timeouts':[{'residue':r,'timeout_seconds':90,'verdict':'UNRESOLVED'} for r in (100,200)]}
        self.h5={'job':H5_JOB,'pid_live':True,'exit':None}
    def plan(self):return build_plan(self.base,self.sweep,self.manifest,self.h5)
    def test_live_h5_uses_two_workers(self):
        p=self.plan();self.assertEqual(p['limits']['workers'],2);self.assertEqual(p['limits']['memory_gib'],32)
        self.assertEqual(p['residual_residues'],[89,100,200]);self.assertEqual(len(p['reused_parts']),381)
    def test_finished_h5_uses_four_workers(self):
        self.h5.update(pid_live=False,exit='0');p=self.plan();self.assertEqual(p['limits']['workers'],4);self.assertEqual(p['limits']['cpus'],8)
    def test_inconclusive_h5_rejected(self):
        self.h5['pid_live']=False
        with self.assertRaises(ValueError):self.plan()
    def test_wrong_h5_job_rejected(self):
        self.h5['job']='other'
        with self.assertRaises(ValueError):self.plan()
    def test_partial_sweep_rejected(self):
        self.sweep['status']='PARTIAL_SWEEP_ARTIFACT_AUDIT'
        with self.assertRaises(ValueError):self.plan()
    def test_failed_sweep_rejected(self):
        self.sweep['authoritative_exit']=1
        with self.assertRaises(ValueError):self.plan()
    def test_missing_attempt_rejected(self):
        self.sweep['attempted_residues'].pop()
        with self.assertRaises(ValueError):self.plan()
    def test_overlapping_outcomes_rejected(self):
        self.sweep['new_timeouts'][0]['residue']=90
        with self.assertRaises(ValueError):self.plan()
    def test_missing_accepted_object_rejected(self):
        self.sweep['accepted_parts'].pop()
        with self.assertRaises(ValueError):self.plan()
    def test_incorrect_timeout_cap_rejected(self):
        self.sweep['new_timeouts'][0]['timeout_seconds']=12
        with self.assertRaises(ValueError):self.plan()
    def test_changed_baseline_source_rejected(self):
        self.base['accepted_parts'][0]['source_sha256']='wrong'
        with self.assertRaises(ValueError):self.plan()
    def test_changed_sweep_source_rejected(self):
        self.sweep['accepted_parts'][0]['source_sha256']='wrong'
        with self.assertRaises(ValueError):self.plan()
    def test_extra_axiom_rejected(self):
        self.sweep['accepted_parts'][0]['axiom_exports'][0]['axioms'].append('sorryAx')
        with self.assertRaises(ValueError):self.plan()
    def test_different_math_pin_rejected(self):
        self.base['math_commit']='wrong'
        with self.assertRaises(ValueError):self.plan()
if __name__=='__main__':unittest.main()
