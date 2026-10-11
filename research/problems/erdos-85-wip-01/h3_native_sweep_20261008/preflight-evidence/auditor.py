"""Independent read-only campaign/preflight audit, with explicit terminal job pin."""
import base64,hashlib,json,re,subprocess
from datetime import datetime
from pathlib import Path
from common import load_inputs,sha,parse_axioms,part_expectation,cell_expectation
REPO=Path('/opt/e85/wt/erdos85__h3-triple-formal-20261007')
AREA='research/problems/erdos-85-wip-01/h3_native_sweep_20261008'
ROOT=REPO/AREA
CACHE=Path('/var/lib/docker/volumes/lean-build-erdos85__h3-triple-formal-20261007/_data')
def info(path):
    code='import pathlib,hashlib,json,sys;p=pathlib.Path(sys.argv[1]);s=p.stat();print(json.dumps({"sha256":hashlib.sha256(p.read_bytes()).hexdigest(),"bytes":s.st_size,"mtime":s.st_mtime}))'
    return json.loads(subprocess.check_output(['sudo','python3','-c',code,str(path)]))
def main(config):
    job=Path('/opt/e85/jobs')/config['job']
    if not (job/'exit').exists():
        pid=int((job/'pid').read_text());print(json.dumps({'status':'PENDING','pid':pid,'pid_live':Path(f'/proc/{pid}').exists()}));return
    files={'job.'+n:(job/n).read_bytes() for n in ('log','spec','exit')}
    raw=files['job.log'].decode();rc=int(files['job.exit'])
    assert re.findall(r'^\[e85\] commit ([a-f0-9]{40}) ',raw,re.M)==[config['commit']]
    for name in ('PLAN.json','run.py','common.py','prepare.py'):
        data=subprocess.check_output(['git','-C',str(REPO),'show',config['commit']+':'+AREA+'/'+name])
        assert data==(ROOT/name).read_bytes();files[name]=data
    plan,manifest,prior,inputs=load_inputs(ROOT,REPO)
    for name,entry in plan['inputs'].items():
        assert inputs[name]==subprocess.check_output(['git','-C',str(REPO),'show',config['commit']+':'+entry['path']])
        files['inputs/'+name+('.lean' if name=='cell_source' else '.py' if name=='generator' else '.json')]=inputs[name]
    for line in ('MEM_GB=16','THREADS=1','CPUS=2','FULL=1'):
        assert line in files['job.spec'].decode().splitlines()
    prerequisites=[]
    for row in prior['results']:
        path='proofs/Proofs/'+row['module']+'.lean';data=(REPO/path).read_bytes()
        assert sha(data)==row['source_sha256']
        assert data==subprocess.check_output(['git','-C',str(REPO),'show',config['commit']+':'+path])
        obj=info(CACHE/'lib/lean/Proofs'/(row['module']+'.olean'));assert obj['sha256']==row['olean_sha256']
        prerequisites.append({'module':row['module'],'source_sha256':sha(data),'object':obj})
    assert info(CACHE/'ir/Proofs/Erdos85H3TripleCompletionRuntime.c')['sha256']==prior['runtime_c']['sha256']
    reused=[]
    for row in plan['reused_parts']:
        obj=info(CACHE/'lib/lean/Proofs'/(row['module'].split('.')[-1]+'.olean'))
        assert obj['sha256']==row['object_sha256'] and obj['bytes']==row['object_bytes'];reused.append(row['residue'])
    report={'job':job.name,'execution_commit':config['commit'],'authoritative_exit':rc,'prerequisites':prerequisites,
            'reused_residues':reused,'scope':plan['scope']}
    if config['preflight']:
        assert rc==0 and 'TIMEOUT=3m' in files['job.spec'].decode().splitlines()
        marker='{\n  "status": "READ_ONLY_PREFLIGHT_PASS",';assert raw.count(marker)==1
        receipt,_=json.JSONDecoder().raw_decode(raw[raw.index(marker):])
        assert receipt['plan_sha256']==sha(files['PLAN.json'])
        assert receipt['reused_objects_checked']==90 and receipt['new_parts']==293 and receipt['known_timeouts']==[89]
        assert receipt['cgroup_memory_bytes']==16*1024**3
        q,p=map(int,receipt['cgroup_cpu_max'].split());assert q==p*2
        assert not (ROOT/'attempt1').exists()
        report.update(status='SWEEP_PREFLIGHT_AUDIT_PASS',receipt=receipt,accepted_new_residues=[])
    else:
        assert 'TIMEOUT=2h' in files['job.spec'].decode().splitlines()
        out=ROOT/'attempt1';files['RUN.json']=(out/'RUN.json').read_bytes();run=json.loads(files['RUN.json'])
        assert run['plan_sha256']==sha(files['PLAN.json']) and run['reused_residues']==reused
        assert run['cgroup_memory_bytes']==16*1024**3
        q,p=map(int,run['cgroup_cpu_max'].split());assert q==2*p
        start=datetime.fromisoformat(run['started_utc']).timestamp();finish=(job/'exit').stat().st_mtime
        steps={x['name']:x for x in run['steps']};assert len(steps)==len(run['steps'])
        full_step_names=['shared']+[f'part{r:03d}' for r in plan['remaining_residues']]
        assert list(steps)==full_step_names[:len(steps)]
        if 'shared' in steps:
            assert steps['shared']['command']==['leanc','-O3','-DLEAN_EXPORTING','-shared','-fPIC','/workspace/proofs/.lake/build/ir/Proofs/Erdos85H3TripleCompletionRuntime.c','-o','/workspace/'+AREA+'/attempt1/libH3TripleRuntime.so']
        for name,s in steps.items():
            files[name+'.log']=(out/(name+'.log')).read_bytes();assert sha(files[name+'.log'])==s['log_sha256']
            assert s['timeout_seconds']==(60 if name=='shared' else 90)
            assert 0<s['effective_timeout_seconds']<=s['timeout_seconds']
        library=out/'libH3TripleRuntime.so'
        if 'library' in run:
            assert sha(library.read_bytes())==run['library']['sha256'] and library.stat().st_size==run['library']['bytes']
        assert run['initializer']=='initialize_proofs_Proofs_Erdos85H3TripleCompletionRuntime'
        assert run['known_timeouts']==plan['known_timeouts']==[89]
        attempts=run['attempts']
        assert [x['residue'] for x in attempts]==plan['remaining_residues'][:len(attempts)]
        assert all(x['status'] in ('COMPILED_PENDING_AUDIT','TIMEOUT') for x in attempts)
        assert [x['residue'] for x in run['parts']]==[x['residue'] for x in attempts if x['status']=='COMPILED_PENDING_AUDIT']
        assert [x['residue'] for x in run['timeouts']]==[x['residue'] for x in attempts if x['status']=='TIMEOUT']
        accepted=[]
        def accept(item,name,source_hash,expected):
            module=item['module'].split('.')[-1];rel='Proofs/'+module+'.lean'
            source=(out/'sources'/rel).read_bytes();assert sha(source)==source_hash==item['source_sha256']
            files['sources/'+rel]=source
            assert not (REPO/'proofs'/rel).exists()
            step=steps[name];assert step['returncode']==0 and step['stop_reason'] is None
            command=['lean','-j1']+(['--plugin=/workspace/'+AREA+'/attempt1/libH3TripleRuntime.so='+run['initializer']] if name!='cell' else [])+[rel,'-o','/workspace/proofs/.lake/build/lib/lean/Proofs/'+module+'.olean']
            assert step['command']==command
            exports=parse_axioms(files[name+'.log'].decode(),expected);assert exports==item['axiom_exports']
            data=(out/'objects'/(module+'.olean')).read_bytes()
            actual=info(CACHE/'lib/lean/Proofs'/(module+'.olean'))
            assert actual=={'sha256':item['object_sha256'],'bytes':item['object_bytes'],'mtime':item['object_mtime']}
            assert sha(data)==actual['sha256'] and len(data)==actual['bytes']>0
            assert start<=actual['mtime']<=finish
            return {**item,'elapsed_seconds':step['elapsed_seconds']}
        for item in run['parts']:
            r=item['residue'];row=manifest['parts'][r]
            assert item['module']==row['module']
            accepted.append(accept(item,f'part{r:03d}',row['source_sha256'],part_expectation(row)))
        # Preserve unsuccessful staged-source snapshots as evidence too, with no credit.
        for source in (out/'sources').rglob('*.lean'):
            files['sources/'+str(source.relative_to(out/'sources'))]=source.read_bytes()
        report.update(accepted_parts=accepted,accepted_new_residues=[x['residue'] for x in accepted],worker_status=run['status'])
        timeouts=[]
        for item in run['timeouts']:
            r=item['residue'];row=manifest['parts'][r];name=f'part{r:03d}';step=steps[name]
            assert step['stop_reason']=='TIMEOUT' and step['returncode']!=0 and step['effective_timeout_seconds']==90
            assert step['command']==['lean','-j1','--plugin=/workspace/'+AREA+'/attempt1/libH3TripleRuntime.so='+run['initializer'],row['source_path'],'-o','/workspace/proofs/.lake/build/lib/lean/Proofs/'+row['module'].split('.')[-1]+'.olean']
            assert sha(files['sources/'+row['source_path']])==row['source_sha256']
            assert not (REPO/'proofs'/row['source_path']).exists()
            missing=subprocess.run(['sudo','test','-e',str(CACHE/'lib/lean/Proofs'/(row['module'].split('.')[-1]+'.olean'))]).returncode
            assert missing==1,'Unaccepted timeout object still in cache'
            if 'unaccepted_object' in item:
                artifact=item['unaccepted_object']
                assert artifact['path']=='unaccepted-objects/'+row['module'].split('.')[-1]+'.olean'
                data=(out/artifact['path']).read_bytes();assert sha(data)==artifact['sha256'] and len(data)==artifact['bytes']
            timeouts.append({'residue':r,'timeout_seconds':90,'elapsed_seconds':step['elapsed_seconds'],'verdict':'UNRESOLVED'})
        report.update(known_timeouts=[89],new_timeouts=timeouts,attempted_residues=[x['residue'] for x in attempts],
                      whole_cell_verified=False)
        if rc==0:
            assert run['status']=='SWEEP_COMPLETED_PENDING_AUDIT' and len(attempts)==293
            report['status']='H3_SWEEP_ARTIFACT_AUDIT_PASS'
        else:
            assert run['status'] in ('STOP','TIMEOUT','BUDGET_STOP','COMPILE_FAILURE','ALARM')
            report['status']='PARTIAL_SWEEP_ARTIFACT_AUDIT'
    assert (job/'log').read_bytes()==files['job.log']
    report['retained_sha256']={n:sha(b) for n,b in files.items()}
    print(json.dumps({'audit':report,'files':{n:base64.b64encode(b).decode() for n,b in files.items()}}))
