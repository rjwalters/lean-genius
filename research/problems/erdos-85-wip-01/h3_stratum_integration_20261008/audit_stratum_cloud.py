"""Independently inspect a terminal H3 stratum compile; never executes Lean."""
import base64,json,re,subprocess
from datetime import datetime
from pathlib import Path
from transfer_pair import sha
from stratum_inputs import load
REPO=Path('/opt/e85/wt/erdos85__h3-triple-formal-20261007')
AREA='research/problems/erdos-85-wip-01/h3_stratum_integration_20261008'
ROOT=REPO/AREA
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
    if not (job/'exit').exists():
        pid=int((job/'pid').read_text());print(json.dumps({'status':'PENDING','pid':pid,'pid_live':Path(f'/proc/{pid}').exists()}));return
    files={'job.'+n:(job/n).read_bytes() for n in ('log','spec','exit')}
    raw=files['job.log'].decode();rc=int(files['job.exit'])
    assert re.findall(r'^\[e85\] commit ([a-f0-9]{40}) ',raw,re.M)==[config['commit']]
    for name in ('SOURCE.json','INTEGRATION.json','run_stratum.py','stratum_inputs.py','transfer_pair.py'):
        data=subprocess.check_output(['git','-C',str(REPO),'show',config['commit']+':'+AREA+'/'+name])
        assert data==(ROOT/name).read_bytes();files[name]=data
    spec,objects,inputs=load(ROOT,REPO,config['triple_audit_sha'],config['transfer_receipt_sha'])
    for name,data in inputs.items():files['inputs/'+name]=data
    for line in ('MEM_GB=16','THREADS=1','CPUS=2','FULL=1','TIMEOUT=3m'):
        assert line in files['job.spec'].decode().splitlines()
    out=ROOT/'stratum-attempt1';files['RUN.json']=(out/'RUN.json').read_bytes();run=json.loads(files['RUN.json'])
    files['compile.log']=(out/'compile.log').read_bytes();assert sha(files['compile.log'])==run['log_sha256']
    assert run['input_sha256']=={n:sha(b) for n,b in inputs.items()}
    assert run['imported_objects']==objects and len(objects)==417
    assert run['cgroup_memory_bytes']==16*1024**3
    quota,period=map(int,run['cgroup_cpu_max'].split());assert quota==2*period
    assert run['command']==['lean','-j1','Proofs/Erdos85H3Stratum.lean','-o','/workspace/proofs/.lake/build/lib/lean/Proofs/Erdos85H3Stratum.olean']
    assert run['timeout_seconds']==90
    for module,row in spec['sources'].items():
        relative='proofs/Proofs/'+module+'.lean';data=(REPO/relative).read_bytes()
        assert data==subprocess.check_output(['git','-C',str(REPO),'show',config['commit']+':'+relative])
        assert sha(data)==row['source_sha256'];files['sources/'+module+'.lean']=data
    for module,digest in spec['shared_pair_dependency_sources'].items():
        relative='proofs/Proofs/'+module+'.lean';data=(REPO/relative).read_bytes()
        assert sha(data)==digest and data==subprocess.check_output(['git','-C',str(REPO),'show',config['commit']+':'+relative])
    modules=list(objects)+(['Erdos85H3Stratum'] if rc==0 else [])
    actual=objects_info(modules)
    for module,row in objects.items():
        assert actual[module]['sha256']==row['sha256'] and actual[module]['bytes']==row['bytes']
    report={'job':job.name,'execution_commit':config['commit'],'authoritative_exit':rc,
            'status':'H3_STRATUM_COMPILE_FAILED','scope':'H3 stratum only; not global order-49 exclusion or paper publication.'}
    if rc==0:
        assert run['status']=='STRATUM_COMPILED_PENDING_AUDIT' and run['returncode']==0 and not run['timed_out']
        raw=files['compile.log'].decode();assert not re.search(r'\b(sorry|error)\b',raw,re.I)
        matches=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",raw)
        assert len(matches)==1 and matches[0][0]==spec['stratum_export']
        axioms=[a.strip() for a in matches[0][1].split(',') if a.strip()]
        assert len(axioms)==len(set(axioms))==411 and set(axioms)==set(spec['expected_stratum_axioms'])
        assert axioms==run['axioms']
        obj=actual['Erdos85H3Stratum'];data=(out/'Erdos85H3Stratum.olean').read_bytes()
        assert sha(data)==obj['sha256']==run['object_sha256'] and len(data)==obj['bytes']==run['object_bytes']>0
        assert obj['mtime']==run['object_mtime']
        assert datetime.fromisoformat(run['started_utc']).timestamp()<=obj['mtime']<=(job/'exit').stat().st_mtime
        report.update(status='H3_STRATUM_ARTIFACT_AUDIT_PASS',theorem=spec['stratum_export'],axioms=axioms,
                      object=obj,elapsed_seconds=run['elapsed_seconds'])
    assert actual==objects_info(modules),'Objects changed during audit'
    assert files['job.log']==(job/'log').read_bytes()
    report['retained_sha256']={n:sha(b) for n,b in files.items()}
    print(json.dumps({'audit':report,'files':{n:base64.b64encode(b).decode() for n,b in files.items()}}))
