"""Independent read-only audit of the final H3 triple-cell assembly."""
import base64,json,re,subprocess
from datetime import datetime
from pathlib import Path
from common import load_inputs,sha,parse_axioms
AREA='research/problems/erdos-85-wip-01/h3_cell_assembly_20261008'
REPO=Path('/opt/e85/wt/erdos85__h3-triple-formal-20261007');ROOT=REPO/AREA
CACHE=Path('/var/lib/docker/volumes/lean-build-erdos85__h3-triple-formal-20261007/_data/lib/lean/Proofs')
def object_infos(modules):
    code='''from pathlib import Path
import sys,json,hashlib
base=Path(sys.argv[1]);result={}
for m in sys.argv[2:]:
 p=base/(m+'.olean')
 if p.exists():
  s=p.stat();result[m]={'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':s.st_size,'mtime':s.st_mtime}
 else:result[m]=None
print(json.dumps(result))'''
    return json.loads(subprocess.check_output(['sudo','python3','-c',code,str(CACHE),*modules]))
def main(config):
    job=Path('/opt/e85/jobs')/config['job']
    if not (job/'exit').exists():
        pid=int((job/'pid').read_text());print(json.dumps({'status':'PENDING','pid':pid,'pid_live':Path(f'/proc/{pid}').exists()}));return
    files={'job.'+n:(job/n).read_bytes() for n in ('log','spec','exit')};raw=files['job.log'].decode();rc=int(files['job.exit'])
    assert re.findall(r'^\[e85\] commit ([a-f0-9]{40}) ',raw,re.M)==[config['commit']]
    for name in ('PLAN.json','prepare.py','common.py','run.py','audit_cloud.py'):
        data=subprocess.check_output(['git','-C',str(REPO),'show',config['commit']+':'+AREA+'/'+name])
        assert data==(ROOT/name).read_bytes();files[name]=data
    plan,manifest,prior,inputs=load_inputs(ROOT,REPO)
    for n,entry in plan['inputs'].items():
        assert inputs[n]==subprocess.check_output(['git','-C',str(REPO),'show',config['commit']+':'+entry['path']])
        files['inputs/'+n+Path(entry['path']).suffix]=inputs[n]
    for line in ('MEM_GB=16','THREADS=1','CPUS=2','FULL=1','TIMEOUT=3m'):
        assert line in files['job.spec'].decode().splitlines()
    imported={r['module']:{'source_sha256':r['source_sha256'],'sha256':r['olean_sha256'],'bytes':r['olean_bytes']} for r in prior['results']}
    assert len(imported)==4
    for row in prior['results']:
        path='proofs/Proofs/'+row['module']+'.lean';data=(REPO/path).read_bytes()
        assert sha(data)==row['source_sha256']
        assert data==subprocess.check_output(['git','-C',str(REPO),'show',config['commit']+':'+path])
    for row in plan['parts']:
        module=row['module'].split('.')[-1];assert module not in imported
        imported[module]={'source_sha256':row['source_sha256'],'sha256':row['object_sha256'],'bytes':row['object_bytes']}
    assert len(imported)==388
    module=plan['cell']['module'].split('.')[-1];objects=object_infos([*imported,module])
    for m,expected in imported.items():
        assert objects[m] and objects[m]['sha256']==expected['sha256'] and objects[m]['bytes']==expected['bytes']
    report={'job':job.name,'execution_commit':config['commit'],'authoritative_exit':rc,'math_commit':plan['math_commit'],
            'reused_residues':list(range(384)),'accepted_new_residues':[],'imported_objects':imported,'scope':plan['scope']}
    if config['preflight']:
        assert rc==0 and objects[module] is None
        marker='{\n  "status": "READ_ONLY_PREFLIGHT_PASS",';assert raw.count(marker)==1
        receipt,_=json.JSONDecoder().raw_decode(raw[raw.index(marker):])
        assert receipt['plan_sha256']==sha(files['PLAN.json']) and receipt['parts_checked']==384 and receipt['prerequisites_checked']==4
        assert receipt['cgroup_memory_bytes']==16*1024**3
        q,p=map(int,receipt['cgroup_cpu_max'].split());assert q==2*p
        assert not (ROOT/'attempt1').exists()
        report.update(status='CELL_ASSEMBLY_PREFLIGHT_AUDIT_PASS',receipt=receipt)
    else:
        out=ROOT/'attempt1';files['RUN.json']=(out/'RUN.json').read_bytes();run=json.loads(files['RUN.json'])
        assert run['plan_sha256']==sha(files['PLAN.json']) and run['imported_residues']==list(range(384))
        assert run['cgroup_memory_bytes']==16*1024**3
        q,p=map(int,run['cgroup_cpu_max'].split());assert q==2*p
        rel='Proofs/'+module+'.lean';files['sources/'+rel]=(out/'sources'/rel).read_bytes()
        assert files['sources/'+rel]==inputs['cell_source'] and not (REPO/'proofs'/rel).exists()
        if (out/'compile.log').exists():files['compile.log']=(out/'compile.log').read_bytes()
        if 'step' in run:
            s=run['step'];assert s['command']==['lean','-j1',rel,'-o','/workspace/proofs/.lake/build/lib/lean/Proofs/'+module+'.olean']
            assert s['timeout_seconds']==90 and 0<=s['effective_timeout_seconds']<=90
            if s['launched']:assert sha(files['compile.log'])==s['log_sha256']
        report['worker_status']=run['status']
        if rc==0:
            assert run['status']=='CELL_COMPILED_PENDING_AUDIT' and run['step']['returncode']==0 and run['step']['stop_reason'] is None
            item=run['cell'];assert item['module']==plan['cell']['module'] and item['source_sha256']==sha(inputs['cell_source'])
            exports=parse_axioms(files['compile.log'].decode(),plan['expected_exports']);assert exports==item['axiom_exports']
            obj=objects[module];assert obj=={'sha256':item['object_sha256'],'bytes':item['object_bytes'],'mtime':item['object_mtime']}
            data=(out/(module+'.olean')).read_bytes();assert sha(data)==obj['sha256'] and len(data)==obj['bytes']>0
            start=datetime.fromisoformat(run['started_utc']).timestamp();finish=(job/'exit').stat().st_mtime
            assert start<=obj['mtime']<=finish
            report.update(status='H3_TRIPLE_CELL_ARTIFACT_AUDIT_PASS',accepted_parts=plan['parts'],cell=item,whole_cell_verified=True)
        else:
            assert run['status'] in ('TIMEOUT','BUDGET_STOP','STOP','COMPILE_FAILURE','ALARM') and objects[module] is None
            if 'unaccepted_object' in run:
                data=(out/'unaccepted.olean').read_bytes();assert sha(data)==run['unaccepted_object']['sha256'] and len(data)==run['unaccepted_object']['bytes']
            report.update(status='CELL_ASSEMBLY_NOT_ACCEPTED',whole_cell_verified=False)
    assert objects==object_infos([*imported,module]),'Object changed during collection'
    assert files['job.log']==(job/'log').read_bytes()
    report['retained_sha256']={n:sha(b) for n,b in files.items()}
    print(json.dumps({'audit':report,'files':{n:base64.b64encode(b).decode() for n,b in files.items()}}))
