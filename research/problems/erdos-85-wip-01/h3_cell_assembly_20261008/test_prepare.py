"""Synthetic future audit fixtures; no Lean or finite search."""
import copy,json,unittest
from prepare import ROOT,complete_ledger
class CoverageChecks(unittest.TestCase):
    def setUp(self):
        base=ROOT.parent
        self.manifest=json.loads((base/'h3_native_parts_20261008/MANIFEST.json').read_text())
        self.baseline=json.loads((base/'h3_native_campaign_20261008/ACCEPTANCE.json').read_text())
        self.sample=json.loads((base/'h3_native_parts_20261008/sample-evidence/AUDIT.json').read_text())
        self.prefix=json.loads((base/'h3_native_campaign_20261008/campaign-evidence1/AUDIT.json').read_text())
        attempted=[r for r in range(384) if r not in self.baseline['accepted_unique_residues'] and r!=89]
        def part(r):
            model=self.manifest['parts'][r]
            return {'residue':r,'module':model['module'],'source_sha256':model['source_sha256'],'object_sha256':'0'*64,'object_bytes':1,
                    'axiom_exports':[{'theorem':model['theorem'],'axioms':['propext','Quot.sound',model['native_axiom']]}]}
        fresh=[r for r in attempted if r!=134]
        self.sweep={'status':'H3_SWEEP_ARTIFACT_AUDIT_PASS','authoritative_exit':0,'job':'synthetic-sweep','execution_commit':'a'*40,
                    'attempted_residues':attempted,'known_timeouts':[89],'accepted_parts':[part(r) for r in fresh],
                    'accepted_new_residues':fresh,'new_timeouts':[{'residue':134,'timeout_seconds':90,'verdict':'UNRESOLVED'}]}
        self.residual={'status':'H3_RESIDUAL_ARTIFACT_AUDIT_PASS','authoritative_exit':0,'job':'synthetic-residual','execution_commit':'b'*40,
                       'reused_residues':sorted(self.baseline['accepted_unique_residues']+fresh),'accepted_new_residues':[89,134],
                       'accepted_parts':[part(134),part(89)],'unresolved_residues':[]}
    def ledger(self):return complete_ledger(self.manifest,self.baseline,self.sample,self.prefix,self.sweep,self.residual)
    def reject(self):
        with self.assertRaises(ValueError):self.ledger()
    def test_exact_384_coverage(self):
        parts=self.ledger();self.assertEqual([r['residue'] for r in parts],list(range(384)))
        self.assertEqual(parts[89]['producer_job'],'synthetic-residual')
        self.assertEqual(parts[90]['producer_job'],'synthetic-sweep')
        self.assertEqual(parts[0]['producer_job'],self.sample['job'])
    def test_partial_residual_rejected(self):self.residual['status']='PARTIAL_RESIDUAL_ARTIFACT_AUDIT';self.reject()
    def test_partial_sweep_rejected(self):self.sweep['status']='PARTIAL_SWEEP_ARTIFACT_AUDIT';self.reject()
    def test_failed_residual_rejected(self):self.residual['authoritative_exit']=1;self.reject()
    def test_missing_residual_object_rejected(self):self.residual['accepted_parts'].pop();self.reject()
    def test_duplicate_residual_object_rejected(self):self.residual['accepted_parts'].append(self.residual['accepted_parts'][0]);self.reject()
    def test_duplicate_baseline_rejected(self):self.baseline['accepted_parts'].append(self.baseline['accepted_parts'][0]);self.reject()
    def test_wrong_baseline_producer_rejected(self):self.baseline['accepted_parts'][0]['producer_job']='wrong';self.reject()
    def test_wrong_baseline_object_rejected(self):self.baseline['accepted_parts'][0]['object_sha256']='1'*64;self.reject()
    def test_source_drift_rejected(self):self.residual['accepted_parts'][0]['source_sha256']='1'*64;self.reject()
    def test_wrong_axiom_rejected(self):self.residual['accepted_parts'][0]['axiom_exports'][0]['axioms'][0]='sorryAx';self.reject()
    def test_duplicate_axiom_rejected(self):
        self.residual['accepted_parts'][0]['axiom_exports'][0]['axioms'].append('propext');self.reject()
    def test_wrong_export_rejected(self):self.residual['accepted_parts'][0]['axiom_exports'][0]['theorem']='different';self.reject()
    def test_original_sample_axiom_drift_rejected(self):self.sample['accepted_parts'][0]['axioms'][0]='sorryAx';self.reject()
    def test_wrong_reuse_coverage_rejected(self):self.residual['reused_residues'].pop();self.reject()
    def test_unresolved_part_rejected(self):self.residual['unresolved_residues']=[89];self.reject()
    def test_empty_object_rejected(self):self.residual['accepted_parts'][0]['object_bytes']=0;self.reject()
    def test_invalid_object_hash_rejected(self):self.residual['accepted_parts'][0]['object_sha256']='wrong';self.reject()
    def test_wrong_sweep_timeout_cap_rejected(self):self.sweep['new_timeouts'][0]['timeout_seconds']=12;self.reject()
    def test_wrong_math_pin_rejected(self):self.baseline['math_commit']='wrong';self.reject()
    def test_manifest_coverage_rejected(self):self.manifest['parts'].pop();self.reject()
if __name__=='__main__':unittest.main()
