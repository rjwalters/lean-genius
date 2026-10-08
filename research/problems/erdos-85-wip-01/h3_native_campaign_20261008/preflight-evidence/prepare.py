"""Freeze a bounded campaign plan; source/metadata checks only, never executes Lean."""
from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parent
BASE=ROOT.parent
REPO=ROOT.parents[3]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    paths={
      'manifest':BASE/'h3_native_parts_20261008/MANIFEST.json',
      'generator':BASE/'h3_native_parts_20261008/prepare.py',
      'acceptance':BASE/'h3_native_parts_20261008/ACCEPTANCE.json',
      'sample_audit':BASE/'h3_native_parts_20261008/sample-evidence/AUDIT.json',
      'prerequisite_audit':BASE/'h3_phase3_runtime_20261008/build-evidence/AUDIT.json',
      'assembly_audit':BASE/'h3_assembly_preflight_20261008/evidence1/AUDIT.json',
      'cell_source':BASE/'h3_native_parts_20261008/source-review/Proofs/Erdos85H3TripleCompletionCell.lean'}
    manifest=json.loads(paths['manifest'].read_text());accepted=json.loads(paths['acceptance'].read_text())
    sample=json.loads(paths['sample_audit'].read_text());assembly=json.loads(paths['assembly_audit'].read_text())
    assert sample['status']=='SAMPLE_ARTIFACT_AUDIT_PASS' and assembly['status']=='CONDITIONAL_ASSEMBLY_AUDIT_PASS'
    assert accepted['audit_sha256']==sha(paths['sample_audit'])
    assert accepted['manifest_sha256']==sha(paths['manifest'])
    assert manifest['source_generator_sha256']==sha(paths['generator'])
    assert manifest['cell']['source_sha256']==sha(paths['cell_source'])
    assert accepted['accepted_unique_residues']==[0,3,4,5,162]
    assert sorted(r['residue'] for r in sample['accepted_parts'])==accepted['accepted_unique_residues']
    remaining=[r for r in range(384) if r not in accepted['accepted_unique_residues']]
    assert remaining==accepted['remaining_residues'] and len(remaining)==379
    plan={'status':'PREPARED_NOT_AUTHORIZED_OR_LAUNCHED','math_commit':manifest['math_commit'],
          'modulus':384,'reused_parts':sample['accepted_parts'],'remaining_residues':remaining,
          'inputs':{k:{'path':str(p.relative_to(REPO)),'sha256':sha(p)} for k,p in paths.items()},
          'limits':{'workers':1,'cpus':2,'memory_gib':16,'per_part_seconds':90,'library_seconds':60,
                    'assembly_seconds':90,'worker_seconds':6900,'outer_timeout':'2h','max_outer_cpu_hours':4},
          'execution_order':'ascending remaining residue; shared library first; full cell last only after all parts succeed',
          'stop_conditions':['explicit STOP file, including during active child','first timeout or nonzero compiler return','source/object/axiom drift','worker deadline'],
          'automatic_retry':False,'new_machines':False,'attempt_directory':'attempt1',
          'scope':'H3 triple cell (3,1) only. No old census credit, whole-H3 stratum, global order-49 theorem, or paper publication.'}
    data=(json.dumps(plan,indent=2)+'\n').encode();path=ROOT/'PLAN.json'
    if path.exists():assert path.read_bytes()==data,'Refusing to change frozen plan'
    else:path.write_bytes(data)
    print('PLAN_PREPARED: 379 remaining, 5 reused; no execution authorized or launched.')
if __name__=='__main__':main()
