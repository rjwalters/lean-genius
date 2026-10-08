"""Independent read-only terminal artifact acceptance; never executes Lean."""
import base64,json,re,subprocess
from datetime import datetime
from pathlib import Path
from prepare import ROOT,REPO,MODULE,sha,inputs,closure
AREA='research/problems/erdos-85-wip-01/order49_h3_closed_capstone_20261008'
CACHE=Path('/var/lib/docker/volumes/lean-build-erdos85__h3-triple-formal-20261007/_data/lib/lean/Proofs')
def objects_info(modules):
    code='''import pathlib,hashlib,json,sys
base=pathlib.Path(sys.argv[1]);result={}
for module in sys.argv[2:]:
 p=base/(module+'.olean');s=p.stat();result[module]={'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':s.st_size,'mtime':s.st_mtime}
print(json.dumps(result))'''
    return json.loads(subprocess.check_output(['sudo','python3','-c',code,str(CACHE),*modules]))
def main(config):
    job=Path('/opt/e85/jobs')/config['job']
    if not (job/'exit').exists():print(json.dumps({'status':'PENDING'}));return
    assert not Path('/proc/'+(job/'pid').read_text().strip()).exists()
    files={'job.'+n:(job/n).read_bytes() for n in ('log','spec','exit')}
    assert re.findall(r'^\[e85\] commit ([a-f0-9]{40}) ',files['job.log'].decode(),re.M)==[config['commit']]
    rc=int(files['job.exit']);assert rc==0,'Compile job failed; retain raw job evidence'
    for line in ('MEM_GB=16','THREADS=1','CPUS=2','FULL=1','TIMEOUT=4m'):
        assert line in files['job.spec'].decode().splitlines()
    for n in ('PLAN.json','supplementary.json','transfer.json','prepare.py','run.py','transfer.py','audit_cloud.py','capture.py','capture_transfer.py'):
        b=subprocess.check_output(['git','-C',str(REPO),'show',config['commit']+':'+AREA+'/'+n]);assert b==(ROOT/n).read_bytes();files[n]=b
    plan=json.loads(files['PLAN.json']);_,objects,producers,exports=inputs()
    assert len(objects)==891 and plan['objects']==objects and plan['producers']==producers and plan['exports']==exports
    assert plan['sources']==closure(REPO,MODULE) and len(plan['sources'])==892
    for m,h in plan['sources'].items():
        relative='proofs/Proofs/'+m+'.lean';b=(REPO/relative).read_bytes()
        assert sha(b)==h and b==subprocess.check_output(['git','-C',str(REPO),'show',config['commit']+':'+relative]),m
    files['wrapper.lean']=(REPO/'proofs/Proofs'/(MODULE+'.lean')).read_bytes()
    for key,p in producers.items():files[key+'-AUDIT.json']=(ROOT.parent/p['path']).read_bytes()
    out=ROOT/'attempt1'
    for n in ('RUN.json','BASELINE.json','compile.log','baseline.log'):files[n]=(out/n).read_bytes()
    run=json.loads(files['RUN.json']);baseline=json.loads(files['BASELINE.json']);supplement=json.loads(files['supplementary.json'])
    assert plan['supplementary_sha256']==sha(files['supplementary.json'])
    assert run['status']=='CAPSTONE_H3_COMPILED_PENDING_AUDIT' and run['returncode']==0 and not run['timed_out']
    assert run['plan_sha256']==sha(files['PLAN.json']) and run['transfer_sha256']==sha(files['transfer.json'])
    assert run['log_sha256']==sha(files['compile.log']) and baseline['log_sha256']==sha(files['baseline.log'])
    assert run['timeout_seconds']==90 and run['cgroup_memory_bytes']==16*1024**3
    quota,period=map(int,run['cgroup_cpu_max'].split());assert quota==2*period
    assert run['command']==['lean','-j1','Proofs/'+MODULE+'.lean','-o','/workspace/proofs/.lake/build/lib/lean/Proofs/'+MODULE+'.olean']
    assert baseline['status']=='BASELINE_REBUILD_BYTE_IDENTICAL' and baseline['returncode']==0
    assert baseline['command']==['lean','-j1','Proofs/'+supplement['module']+'.lean','-o','/workspace/'+AREA+'/attempt1/'+supplement['module']+'.olean']
    assert baseline['elapsed_seconds']<90 and run['elapsed_seconds']<90
    fresh=(out/(supplement['module']+'.olean')).read_bytes()
    assert sha(fresh)==baseline['sha256']==supplement['sha256'] and len(fresh)==baseline['bytes']==supplement['bytes']
    assert not re.search(r'\b(sorry|error)\b',files['compile.log'].decode()+files['baseline.log'].decode(),re.I)
    matches=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",files['compile.log'].decode());assert len(matches)==3
    actual_exports=[]
    for (name,raw),expected in zip(matches,exports):
        axioms=[x.strip() for x in raw.split(',') if x.strip()]
        assert name==expected['theorem'] and len(axioms)==len(set(axioms)) and sorted(axioms)==expected['axioms']
        actual_exports.append({'theorem':name,'axioms':axioms})
    assert actual_exports==run['exports']
    actual=objects_info(list(objects)+[MODULE])
    for m,row in objects.items():assert actual[m]['sha256']==row['sha256'] and actual[m]['bytes']==row['bytes'],m
    obj=actual[MODULE];fresh=(out/(MODULE+'.olean')).read_bytes()
    assert obj==run['object'] and sha(fresh)==obj['sha256'] and len(fresh)==obj['bytes']>0
    assert datetime.fromisoformat(run['started_utc']).timestamp()<=obj['mtime']<=(job/'exit').stat().st_mtime
    assert actual==objects_info(list(objects)+[MODULE]),'Objects changed during audit'
    assert files['job.log']==(job/'log').read_bytes()
    report={'status':'H1_H7_CONDITIONAL_CAPSTONE_ARTIFACT_AUDIT_PASS','job':job.name,'execution_commit':config['commit'],'authoritative_exit':rc,'module':MODULE,'object':obj,'exports':actual_exports,'imported_objects':objects,'source_sha256':plan['sources'][MODULE],'baseline_rebuild':baseline,'elapsed_seconds':run['elapsed_seconds'],'unconditional_drop_verified':False,'scope':'H3 and H5 discharged; H1 and H7 evidence remain explicit hypotheses. No paper publication verdict.','retained_sha256':{n:sha(b) for n,b in files.items()}}
    print(json.dumps({'audit':report,'files':{n:base64.b64encode(b).decode() for n,b in files.items()}}))
