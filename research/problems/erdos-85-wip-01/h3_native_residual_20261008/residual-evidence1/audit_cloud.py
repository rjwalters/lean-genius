"""Read-only independent residual audit on the existing builder host."""
import base64,json,re,subprocess
from pathlib import Path
from common import load_inputs,sha
from validate_run import verify_run,AREA
REPO=Path('/opt/e85/wt/erdos85__h3-triple-formal-20261007')
ROOT=REPO/AREA
CACHE=Path('/var/lib/docker/volumes/lean-build-erdos85__h3-triple-formal-20261007/_data')
SCRIPTS=('prepare.py','common.py','process.py','scheduler.py','run.py','validate_run.py','audit_cloud.py')
def info(path):
    code='import pathlib,hashlib,json,sys;p=pathlib.Path(sys.argv[1]);s=p.stat();print(json.dumps({"sha256":hashlib.sha256(p.read_bytes()).hexdigest(),"bytes":s.st_size,"mtime":s.st_mtime}))'
    return json.loads(subprocess.check_output(['sudo','python3','-c',code,str(path)]))
def exists(path):
    rc=subprocess.run(['sudo','test','-e',str(path)]).returncode
    assert rc in (0,1);return rc==0
def main(config):
    job=Path('/opt/e85/jobs')/config['job']
    if not (job/'exit').exists():
        pid=int((job/'pid').read_text());print(json.dumps({'status':'PENDING','pid':pid,'pid_live':Path(f'/proc/{pid}').exists()}));return
    files={'job.'+n:(job/n).read_bytes() for n in ('log','spec','exit')}
    raw=files['job.log'].decode();rc=int(files['job.exit'])
    assert re.findall(r'^\[e85\] commit ([a-f0-9]{40}) ',raw,re.M)==[config['commit']]
    for name in ('PLAN.json',)+SCRIPTS:
        data=subprocess.check_output(['git','-C',str(REPO),'show',config['commit']+':'+AREA+'/'+name])
        assert data==(ROOT/name).read_bytes();files[name]=data
    plan,manifest,prior,inputs=load_inputs(ROOT,REPO);limits=plan['limits']
    for name,entry in plan['inputs'].items():
        assert inputs[name]==subprocess.check_output(['git','-C',str(REPO),'show',config['commit']+':'+entry['path']])
        suffix=Path(entry['path']).suffix;files['inputs/'+name+suffix]=inputs[name]
    specification=files['job.spec'].decode().splitlines()
    for line in ('MEM_GB='+str(limits['memory_gib']),'THREADS='+str(limits['workers']),'CPUS='+str(limits['cpus']),'FULL=1'):
        assert line in specification
    prereqs=[];stable={}
    for row in prior['results']:
        path='proofs/Proofs/'+row['module']+'.lean';data=(REPO/path).read_bytes()
        assert sha(data)==row['source_sha256']
        assert data==subprocess.check_output(['git','-C',str(REPO),'show',config['commit']+':'+path])
        objpath=CACHE/'lib/lean/Proofs'/(row['module']+'.olean');obj=info(objpath)
        assert obj['sha256']==row['olean_sha256'];stable[objpath]=obj
        prereqs.append({'module':row['module'],'source_sha256':sha(data),'object':obj})
    cpath=CACHE/'ir/Proofs/Erdos85H3TripleCompletionRuntime.c'
    cinfo=info(cpath);assert cinfo['sha256']==prior['runtime_c']['sha256'];stable[cpath]=cinfo
    reused=[]
    for row in plan['reused_parts']:
        path=CACHE/'lib/lean/Proofs'/(row['module'].split('.')[-1]+'.olean');obj=info(path)
        assert obj['sha256']==row['object_sha256'] and obj['bytes']==row['object_bytes']
        stable[path]=obj;reused.append(row['residue'])
    report={'job':job.name,'execution_commit':config['commit'],'authoritative_exit':rc,'prerequisites':prereqs,
            'reused_residues':reused,'scope':plan['scope']}
    if config['preflight']:
        assert rc==0 and 'TIMEOUT=3m' in specification
        marker='{\n  "status": "READ_ONLY_PREFLIGHT_PASS",';assert raw.count(marker)==1
        receipt,_=json.JSONDecoder().raw_decode(raw[raw.index(marker):])
        assert receipt['plan_sha256']==sha(files['PLAN.json'])
        assert receipt['reused_objects_checked']==len(reused) and receipt['residual_residues']==plan['residual_residues']
        assert receipt['workers']==limits['workers'] and receipt['cgroup_memory_bytes']==limits['memory_gib']*1024**3
        q,p=map(int,receipt['cgroup_cpu_max'].split());assert q==p*limits['cpus']
        assert not (ROOT/'attempt1').exists()
        report.update(status='RESIDUAL_PREFLIGHT_AUDIT_PASS',receipt=receipt,accepted_new_residues=[])
    else:
        assert 'TIMEOUT=6h' in specification
        out=ROOT/'attempt1';files['RUN.json']=(out/'RUN.json').read_bytes();run=json.loads(files['RUN.json'])
        for path in out.glob('*.log'):files[path.name]=path.read_bytes()
        for path in (out/'sources').rglob('*.lean'):
            rel=path.relative_to(out/'sources');files['sources/'+str(rel)]=path.read_bytes()
            assert not (REPO/'proofs'/rel).exists()
        if 'library' in run:
            data=(out/'libH3TripleRuntime.so').read_bytes()
            assert sha(data)==run['library']['sha256'] and len(data)==run['library']['bytes']>0
        objects={}
        accepted_ids={x['residue'] for x in run['parts']}
        for r in plan['residual_residues']:
            row=manifest['parts'][r];name=row['module'].split('.')[-1]+'.olean';path=CACHE/'lib/lean/Proofs'/name
            if r in accepted_ids:
                objects[r]=info(path);stable[path]=objects[r]
                data=(out/'objects'/name).read_bytes()
                assert sha(data)==objects[r]['sha256'] and len(data)==objects[r]['bytes']
            else:assert not exists(path);objects[r]=None
        for item in run['attempts']:
            if 'unaccepted_object' in item:
                a=item['unaccepted_object'];r=item['residue']
                assert a['path']=='unaccepted-objects/'+manifest['parts'][r]['module'].split('.')[-1]+'.olean'
                data=(out/a['path']).read_bytes();assert sha(data)==a['sha256'] and len(data)==a['bytes']
                files[a['path']]=data
        finish=(job/'exit').stat().st_mtime
        report.update(verify_run(run,plan,manifest,files,objects,finish,rc))
    for path,metadata in stable.items():assert info(path)==metadata,'Artifact changed during audit'
    assert (job/'log').read_bytes()==files['job.log']
    report['retained_sha256']={n:sha(b) for n,b in files.items()}
    print(json.dumps({'audit':report,'files':{n:base64.b64encode(b).decode() for n,b in files.items()}}))
