"""Independent residual receipt checks, given raw files and current object metadata."""
from datetime import datetime
from common import sha,parse_axioms,part_expectation
AREA='research/problems/erdos-85-wip-01/h3_native_residual_20261008'
INIT='initialize_proofs_Proofs_Erdos85H3TripleCompletionRuntime'
def verify_run(run,plan,manifest,files,objects,finish,rc):
    limits=plan['limits'];start=datetime.fromisoformat(run['started_utc']).timestamp()
    assert start<=finish
    assert run['plan_sha256']==sha(files['PLAN.json'])
    assert run['workers']==limits['workers'] and run['cgroup_memory_bytes']==limits['memory_gib']*1024**3
    q,p=map(int,run['cgroup_cpu_max'].split());assert q==limits['cpus']*p
    assert run['initializer']==INIT and run['reused_residues']==[x['residue'] for x in plan['reused_parts']]
    steps={s['name']:s for s in run['steps']};assert len(steps)==len(run['steps'])
    assert set(steps)<={'shared'}|{f'part{r:03d}' for r in plan['residual_residues']}
    library='/workspace/'+AREA+'/attempt1/libH3TripleRuntime.so'
    intervals=[]
    for name,s in steps.items():
        cap=limits['library_seconds'] if name=='shared' else limits['per_part_seconds']
        assert s['timeout_seconds']==cap and 0<=s['effective_timeout_seconds']<=cap
        if not s['launched']:
            assert s['returncode'] is None and s['stop_reason'] in ('STOP','BUDGET_STOP');continue
        assert sha(files[name+'.log'])==s['log_sha256']
        begin=datetime.fromisoformat(s['started_utc']).timestamp();end=datetime.fromisoformat(s['finished_utc']).timestamp()
        assert start<=begin<=end<=finish and s['elapsed_seconds']>=0
        if name!='shared':intervals.extend([(begin,1),(end,-1)])
        if s['stop_reason']=='TIMEOUT':
            assert s['returncode']!=0 and s['effective_timeout_seconds']==cap and s['elapsed_seconds']>=cap
        if s['stop_reason']=='BUDGET_STOP':assert s['effective_timeout_seconds']<cap
        if name=='shared':
            expected=['leanc','-O3','-DLEAN_EXPORTING','-shared','-fPIC','/workspace/proofs/.lake/build/ir/Proofs/Erdos85H3TripleCompletionRuntime.c','-o',library]
        else:
            r=int(name[4:]);row=manifest['parts'][r]
            expected=['lean','-j1','--plugin='+library+'='+INIT,row['source_path'],'-o',
                      '/workspace/proofs/.lake/build/lib/lean/Proofs/'+row['module'].split('.')[-1]+'.olean']
            assert sha(files['sources/'+row['source_path']])==row['source_sha256']
        assert s['command']==expected
    active=0
    for _,delta in sorted(intervals):
        active+=delta;assert 0<=active<=limits['workers']
    assert active==0
    attempts=run['attempts'];ids=[x['residue'] for x in attempts]
    assert len(set(ids))==len(ids) and set(ids)<=set(plan['residual_residues'])
    if 'dispatched_residues' in run:
        dispatched=run['dispatched_residues']
        assert dispatched==plan['residual_residues'][:len(dispatched)] and set(dispatched)==set(ids)
        not_started=[r for r in plan['residual_residues'] if r not in ids or any(x['residue']==r and x['status']=='NOT_STARTED' for x in attempts)]
        assert run['not_started_residues']==not_started
    accepted=[]
    for item in attempts:
        r=item['residue'];row=manifest['parts'][r];name=f'part{r:03d}'
        assert item['status'] in ('COMPILED_PENDING_AUDIT','TIMEOUT','STOP','BUDGET_STOP','ALARM','COMPILE_FAILURE','NOT_STARTED')
        if 'step' in item:assert item['step']==steps[name]
        else:assert item['status'] in ('NOT_STARTED','BUDGET_STOP','ALARM')
        if item['status']=='COMPILED_PENDING_AUDIT':
            step=steps[name]
            assert step['launched'] and step['returncode']==0 and step['stop_reason'] is None
            assert step['effective_timeout_seconds']>0
            assert item['module']==row['module'] and item['source_sha256']==row['source_sha256']
            exports=parse_axioms(files[name+'.log'].decode(),part_expectation(row));assert exports==item['axiom_exports']
            obj=objects[r];assert obj=={'sha256':item['object_sha256'],'bytes':item['object_bytes'],'mtime':item['object_mtime']}
            assert obj['bytes']>0 and start<=obj['mtime']<=finish
            accepted.append({k:v for k,v in item.items() if k!='step'})
        else:
            assert objects.get(r) is None,'Unaccepted object remains reusable'
            if item['status']=='TIMEOUT':assert steps[name]['stop_reason']=='TIMEOUT'
    assert run['parts']==accepted
    assert set(steps)-{'shared'}=={f"part{x['residue']:03d}" for x in attempts if 'step' in x}
    if accepted or rc==0:
        assert steps['shared']['returncode']==0 and steps['shared']['stop_reason'] is None and 'library' in run
    if rc==0:
        assert run['status']=='RESIDUAL_COMPLETED_PENDING_AUDIT'
        assert sorted(x['residue'] for x in accepted)==plan['residual_residues']
        status='H3_RESIDUAL_ARTIFACT_AUDIT_PASS'
    else:
        assert run['status'] in ('STOP','TIMEOUT','BUDGET_STOP','COMPILE_FAILURE','ALARM','NOT_STARTED')
        status='PARTIAL_RESIDUAL_ARTIFACT_AUDIT'
    return {'status':status,'accepted_parts':accepted,'accepted_new_residues':sorted(x['residue'] for x in accepted),
            'attempted_residues':sorted(ids),'unresolved_residues':[r for r in plan['residual_residues'] if r not in {x['residue'] for x in accepted}],
            'worker_status':run['status'],'whole_cell_verified':False}
