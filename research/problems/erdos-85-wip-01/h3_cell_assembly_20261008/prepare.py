"""Freeze the complete 384-part imported-object ledger before H3 cell assembly."""
import argparse,hashlib,json,re
from pathlib import Path
ROOT=Path(__file__).resolve().parent
REPO=ROOT.parents[3]
def sha(data):return hashlib.sha256(data).hexdigest()

def complete_ledger(manifest,baseline,sample,prefix,sweep,residual):
    if manifest['modulus']!=384 or [p['residue'] for p in manifest['parts']]!=list(range(384)):
        raise ValueError('Wrong part inventory')
    if baseline['math_commit']!=manifest['math_commit'] or baseline['status']!='PARTIAL_ACCEPTANCE':
        raise ValueError('Wrong accepted baseline')
    if baseline['accepted_unique_residues']!=list(range(89))+[162]:raise ValueError('Baseline coverage changed')
    if sample['status']!='SAMPLE_ARTIFACT_AUDIT_PASS' or sample['authoritative_exit']!=0:
        raise ValueError('Original sample audit required')
    if prefix['status']!='PARTIAL_CAMPAIGN_ARTIFACT_AUDIT':raise ValueError('Original accepted prefix audit required')
    if sweep['status']!='H3_SWEEP_ARTIFACT_AUDIT_PASS' or sweep['authoritative_exit']!=0:
        raise ValueError('Complete sweep audit required')
    if residual['status']!='H3_RESIDUAL_ARTIFACT_AUDIT_PASS' or residual['authoritative_exit']!=0:
        raise ValueError('Complete residual audit required')
    parts={}
    def add(row,audit):
        r=row['residue']
        if type(r) is not int or not 0<=r<384 or r in parts:raise ValueError('Invalid or duplicate residue')
        model=manifest['parts'][r]
        if row['module']!=model['module'] or row['source_sha256']!=model['source_sha256']:
            raise ValueError('Part source differs from frozen inventory')
        expected={'propext','Quot.sound',model['native_axiom']}
        exports=([{'theorem':row['theorem'],'axioms':row['axioms']}] if audit['status']=='SAMPLE_ARTIFACT_AUDIT_PASS'
                 else row['axiom_exports'])
        if len(exports)!=1 or exports[0]['theorem']!=model['theorem'] or len(exports[0]['axioms'])!=3 or set(exports[0]['axioms'])!=expected:
            raise ValueError('Wrong native-part axiom set')
        if not re.fullmatch('[a-f0-9]{64}',row['object_sha256']) or type(row['object_bytes']) is not int or row['object_bytes']<=0:
            raise ValueError('Invalid object metadata')
        parts[r]={'residue':r,'module':row['module'],'theorem':model['theorem'],'source_sha256':row['source_sha256'],
                  'object_sha256':row['object_sha256'],'object_bytes':row['object_bytes'],'axioms':exports[0]['axioms'],
                  'producer_job':audit['job'],'execution_commit':audit['execution_commit']}
    for audit in (sample,prefix):
        for row in audit['accepted_parts']:add(row,audit)
    if sorted(parts)!=baseline['accepted_unique_residues']:raise ValueError('Audited baseline coverage differs')
    if [r['residue'] for r in baseline['accepted_parts']]!=baseline['accepted_unique_residues']:
        raise ValueError('Baseline ledger contains duplicate or missing objects')
    for row in baseline['accepted_parts']:
        actual=parts[row['residue']]
        if any(row[k]!=actual[k] for k in ('module','source_sha256','object_sha256','object_bytes','producer_job','execution_commit')):
            raise ValueError('Baseline object differs from original independent audit')
    unattempted=[r for r in range(384) if r not in parts and r!=89]
    if sweep['attempted_residues']!=unattempted or sweep['known_timeouts']!=[89]:raise ValueError('Incomplete sweep')
    fresh=[r['residue'] for r in sweep['accepted_parts']];timeouts=[r['residue'] for r in sweep['new_timeouts']]
    if fresh!=sweep['accepted_new_residues'] or len(set(fresh+timeouts))!=293 or sorted(fresh+timeouts)!=unattempted:
        raise ValueError('Sweep outcomes overlap or omit residues')
    if any(r['timeout_seconds']!=90 or r['verdict']!='UNRESOLVED' for r in sweep['new_timeouts']):
        raise ValueError('Wrong residual classification')
    for row in sweep['accepted_parts']:add(row,sweep)
    remaining=sorted([89]+timeouts)
    if residual['reused_residues']!=sorted(parts):raise ValueError('Residual reuse coverage differs')
    if residual['accepted_new_residues']!=remaining or residual['unresolved_residues']:
        raise ValueError('Residual parts remain unresolved')
    if sorted(r['residue'] for r in residual['accepted_parts'])!=remaining:raise ValueError('Residual artifact coverage differs')
    for row in residual['accepted_parts']:add(row,residual)
    if sorted(parts)!=list(range(384)):raise ValueError('Full 384-way coverage required')
    return [parts[r] for r in range(384)]

def main():
    p=argparse.ArgumentParser();p.add_argument('--residual-audit',type=Path,required=True);a=p.parse_args()
    old=json.loads((ROOT.parent/'h3_native_sweep_20261008/PLAN.json').read_text())
    paths={n:REPO/entry['path'] for n,entry in old['inputs'].items()}
    paths.update(baseline=ROOT.parent/'h3_native_campaign_20261008/ACCEPTANCE.json',
                 sweep_audit=ROOT.parent/'h3_native_sweep_20261008/sweep-evidence1/AUDIT.json',
                 residual_audit=a.residual_audit.resolve(),
                 process_helper=ROOT.parent/'h3_native_residual_20261008/process.py')
    raw={n:p.read_bytes() for n,p in paths.items()}
    for n,entry in old['inputs'].items():
        if sha(raw[n])!=entry['sha256']:raise ValueError('Original source/audit input changed: '+n)
    data={n:json.loads(raw[n]) for n in ('manifest','baseline','sample_audit','prefix_audit','sweep_audit','residual_audit','prerequisite_audit')}
    for n in ('sample_audit','prefix_audit','sweep_audit','residual_audit'):
        for filename,digest in data[n]['retained_sha256'].items():
            if sha((paths[n].parent/filename).read_bytes())!=digest:raise ValueError('Raw producer evidence changed: '+filename)
    parts=complete_ledger(*(data[n] for n in ('manifest','baseline','sample_audit','prefix_audit','sweep_audit','residual_audit')))
    manifest=data['manifest'];runtime=data['prerequisite_audit']
    if runtime['status']!='RUNTIME_HELPERS_CHAIN_BUILD_AUDIT_PASS' or runtime['execution_commit']!=manifest['math_commit']:
        raise ValueError('Wrong runtime prerequisite audit')
    if sha(raw['cell_source'])!=manifest['cell']['source_sha256']:raise ValueError('Reviewed cell source changed')
    axioms=sorted({'propext','Classical.choice','Quot.sound'}|{r['native_axiom'] for r in manifest['parts']})
    if len(axioms)!=387:raise ValueError('Unexpected full-cell axiom set')
    plan={'status':'PREPARED_NOT_COMPILED','math_commit':manifest['math_commit'],'parts':parts,
          'cell':manifest['cell'],'limits':{'workers':1,'cpus':2,'memory_gib':16,'compile_seconds':90,'outer_timeout':'3m'},
          'inputs':{n:{'path':str(p.relative_to(REPO)),'sha256':sha(raw[n])} for n,p in paths.items()},
          'expected_exports':{'Erdos85.H3TripleCompletion.'+name:axioms for name in
              ('threeHighCanonicalRepresentativeExcluded_one','orderFortyNineTripleCellExcluded_three_one')},
          'scope':'Compile and independently audit the reviewed H3 triple cell from all 384 accepted native parts; no native searches or stratum build.'}
    out=ROOT/'PLAN.json';encoded=(json.dumps(plan,indent=2)+'\n').encode()
    if out.exists():
        if out.read_bytes()!=encoded:raise ValueError('Refusing to overwrite a different assembly plan')
    else:
        with out.open('xb') as f:f.write(encoded)
    print('CELL_ASSEMBLY_PLAN_PREPARED: 384 independently accepted imported parts; no compilation.')
if __name__=='__main__':main()
