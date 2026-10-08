"""Prepare the authorized residual pass only after a complete audited H3 sweep."""
from pathlib import Path
from datetime import datetime,timezone
import argparse,hashlib,json,re
ROOT=Path(__file__).resolve().parent
REPO=ROOT.parents[3]
H5_JOB='20261008T112746-erdos85__h5-formal-20261008-455708'
def sha(data):return hashlib.sha256(data).hexdigest()
def choose_workers(h5):
    if h5['job']!=H5_JOB:raise ValueError('Wrong H5 job')
    if h5['exit'] is None and h5['pid_live']:return 2
    if h5['exit'] is not None and not h5['pid_live']:return 4
    raise ValueError('H5 state is inconclusive; reobserve the same job')

def build_plan(baseline,sweep,manifest,h5):
    if [r['residue'] for r in manifest['parts']]!=list(range(384)):raise ValueError('Manifest coverage differs')
    if baseline['status']!='PARTIAL_ACCEPTANCE' or baseline['accepted_unique_residues']!=list(range(89))+[162]:
        raise ValueError('Wrong accepted baseline')
    if baseline['math_commit']!=manifest['math_commit']:raise ValueError('Baseline math pin differs')
    if sweep['status']!='H3_SWEEP_ARTIFACT_AUDIT_PASS' or sweep['authoritative_exit']!=0:
        raise ValueError('Complete independently audited sweep required')
    untested=[r for r in range(384) if r not in baseline['accepted_unique_residues'] and r!=89]
    if sweep['attempted_residues']!=untested or sweep['known_timeouts']!=[89]:raise ValueError('Incomplete sweep coverage')
    new=[p['residue'] for p in sweep['accepted_parts']]
    timed=[p['residue'] for p in sweep['new_timeouts']]
    if new!=sweep['accepted_new_residues']:raise ValueError('Accepted sweep inventory mismatch')
    if len(set(new+timed))!=293 or sorted(new+timed)!=untested:raise ValueError('Duplicate, missing or overlapping outcomes')
    if any(p['timeout_seconds']!=90 or p['verdict']!='UNRESOLVED' for p in sweep['new_timeouts']):raise ValueError('Invalid timeout classification')
    reused=list(baseline['accepted_parts'])
    if [r['residue'] for r in reused]!=baseline['accepted_unique_residues']:raise ValueError('Baseline object coverage mismatch')
    for row in reused:
        model=manifest['parts'][row['residue']]
        if row['module']!=model['module'] or row['source_sha256']!=model['source_sha256']:raise ValueError('Baseline source mismatch')
        if len(row['axioms'])!=3 or set(row['axioms'])!={'propext','Quot.sound',model['native_axiom']}:raise ValueError('Baseline axioms differ')
    for row in sweep['accepted_parts']:
        r=row['residue'];model=manifest['parts'][r]
        if row['module']!=model['module'] or row['source_sha256']!=model['source_sha256']:raise ValueError('Sweep source mismatch')
        reports=row['axiom_exports']
        if len(reports)!=1 or len(reports[0]['axioms'])!=3 or reports[0]['theorem']!=model['theorem'] or set(reports[0]['axioms'])!={'propext','Quot.sound',model['native_axiom']}:
            raise ValueError('Sweep axiom mismatch')
        reused.append({'residue':r,'module':row['module'],'source_sha256':row['source_sha256'],
                       'object_sha256':row['object_sha256'],'object_bytes':row['object_bytes'],
                       'axioms':reports[0]['axioms']})
    reused.sort(key=lambda r:r['residue']);residual=sorted([89]+timed)
    for row in reused:
        if not re.fullmatch('[a-f0-9]{64}',row['object_sha256']) or type(row['object_bytes']) is not int or row['object_bytes']<=0:
            raise ValueError('Invalid accepted object metadata')
    if sorted([r['residue'] for r in reused]+residual)!=list(range(384)):raise ValueError('Global coverage gap')
    workers=choose_workers(h5)
    return {'status':'PREPARED_NOT_LAUNCHED','math_commit':manifest['math_commit'],'modulus':384,
            'reused_parts':reused,'residual_residues':residual,'h5_observation':h5,
            'limits':{'workers':workers,'cpus':workers*2,'memory_gib':workers*16,
                      'per_part_seconds':1800,'library_seconds':60,'worker_seconds':21300,'outer_timeout':'6h'},
            'authorization':{'room_message':53044,'sender':'claude-h5','scope':'Only timed-out residues; 30 min per part; up to 2 workers while H5 live or 4 once finished; 6 h outer cap; stop on any further timeout.'},
            'automatic_retry':False,'stop_policy':'Stop scheduling and terminate active children on first timeout, failure, STOP or global deadline.',
            'scope':'Residual native parts only; final 384-premise cell and stratum builds require separate independent acceptance.'}

def main():
    p=argparse.ArgumentParser();p.add_argument('--h5-observation',type=Path,required=True);a=p.parse_args()
    old=json.loads((ROOT.parent/'h3_native_sweep_20261008/PLAN.json').read_text())
    paths={n:REPO/entry['path'] for n,entry in old['inputs'].items()}
    paths.update({'baseline':ROOT.parent/'h3_native_campaign_20261008/ACCEPTANCE.json',
           'sweep_audit':ROOT.parent/'h3_native_sweep_20261008/sweep-evidence1/AUDIT.json',
           'manifest':ROOT.parent/'h3_native_parts_20261008/MANIFEST.json'})
    raw={n:p.read_bytes() for n,p in paths.items()}
    for n,entry in old['inputs'].items():
        if sha(raw[n])!=entry['sha256']:raise ValueError('Original sweep input changed: '+n)
    data={n:json.loads(raw[n]) for n in ('baseline','sweep_audit','manifest')}
    sweep=data['sweep_audit']
    for n,digest in sweep['retained_sha256'].items():
        if sha((paths['sweep_audit'].parent/n).read_bytes())!=digest:raise ValueError('Sweep evidence changed: '+n)
    h5=json.loads(a.h5_observation.read_text())
    age=(datetime.now(timezone.utc)-datetime.fromisoformat(h5['observed_utc'])).total_seconds()
    if not 0<=age<=300:raise ValueError('Fresh authoritative H5 observation required (within five minutes)')
    plan=build_plan(data['baseline'],sweep,data['manifest'],h5)
    plan['inputs']={n:{'path':str(p.relative_to(REPO)),'sha256':sha(raw[n])} for n,p in paths.items()}
    plan['h5_observation_sha256']=sha(a.h5_observation.read_bytes())
    encoded=(json.dumps(plan,indent=2)+'\n').encode();out=ROOT/'PLAN.json'
    if out.exists():
        if out.read_bytes()!=encoded:raise ValueError('Refusing to overwrite a different plan')
    else:out.write_bytes(encoded)
    print('RESIDUAL_PLAN_PREPARED:',len(plan['residual_residues']),'parts,',plan['limits']['workers'],'workers. Not launched.')
if __name__=='__main__':main()
