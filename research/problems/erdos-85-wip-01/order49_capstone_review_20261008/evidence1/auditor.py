"""Read-only conditional-capstone artifact audit; exact axioms require review."""
import base64,hashlib,json,re,subprocess
from datetime import datetime
from pathlib import Path
REPO=Path('/opt/e85/wt/erdos85__order49-capstone-20261008')
CACHE=Path('/var/lib/docker/volumes/lean-build-erdos85__order49-capstone-20261008/_data/lib/lean/Proofs')
def sha(data):return hashlib.sha256(data).hexdigest()
def objects(modules):
    script='''from pathlib import Path
import sys,json,hashlib
base=Path(sys.argv[1]);rows={}
for module in sys.argv[2:]:
 p=base/(module+'.olean')
 if p.exists():
  s=p.stat();rows[module]={'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':s.st_size,'mtime':s.st_mtime}
 else:rows[module]=None
print(json.dumps(rows))'''
    return json.loads(subprocess.check_output(['sudo','python3','-c',script,str(CACHE),*modules]))
def main(config):
    source=config['source'];review=config['axioms'];job=Path('/opt/e85/jobs')/source['job'];pin=source['execution_commit']
    if not (job/'exit').exists():
        pid=int((job/'pid').read_text());print(json.dumps({'status':'PENDING','job':job.name,'pid':pid,'pid_live':Path(f'/proc/{pid}').exists()}));return
    files={'job.'+n:(job/n).read_bytes() for n in ('log','spec','exit')};raw=files['job.log'].decode();rc=int(files['job.exit'])
    assert re.findall(r'^\[e85\] commit ([a-f0-9]{40}) ',raw,re.M)==[pin]
    assert rc==0 and 'Build completed successfully (' in raw and '=== Build succeeded ===' in raw
    assert not re.search(r'\berror:',raw,re.I) and 'sorry' not in raw.lower()
    # The original specification is retained even though the live CPU quota was corrected.
    for line in ('REF=erdos85/order49-capstone-20261008','TARGET=Proofs.Erdos85OrderFortyNineCapstone','MEM_GB=48','TIMEOUT=6h','THREADS=6','CPUS=16'):
        assert line in files['job.spec'].decode().splitlines()
    start=datetime.fromisoformat(re.search(r'^\[e85\] job .* started (\S+)',raw,re.M)[1].replace('Z','+00:00')).timestamp()
    finish=(job/'exit').stat().st_mtime;actual=objects(list(source['sources']));rows=[]
    built=re.findall(r'\] Built Proofs\.([^\s]+) \(([^)]+)\)',raw)
    fresh={}
    for module,elapsed in built:
        assert module not in fresh,'Duplicate fresh build: '+module;fresh[module]=elapsed
    assert source['module'] in fresh
    for module,entry in source['sources'].items():
        path='proofs/Proofs/'+module+'.lean';data=(REPO/path).read_bytes()
        assert sha(data)==entry['source_sha256'],module
        assert data==subprocess.check_output(['git','-C',str(REPO),'show',pin+':'+path]),module
        obj=actual[module];assert obj and obj['bytes']>0 and obj['mtime']<=finish,module
        if module in fresh:assert start<=obj['mtime'],module
        if module in source['audited_imports']:
            assert obj['sha256']==source['audited_imports'][module]['object_sha256'],'Audited import changed: '+module
        rows.append({'module':module,'source_sha256':sha(data),'object':obj,'fresh_build_elapsed':fresh.get(module)})
        if module==source['module']:files['source/'+module+'.lean']=data
    exports=[]
    for theorem,required in source['required_inherited_axioms'].items():
        matches=re.findall(r"info: Proofs/Erdos85OrderFortyNineCapstone\.lean:\d+:\d+: '"+re.escape(theorem)+r"' depends on axioms: \[([^\]]*)\]",raw)
        assert len(matches)==1,theorem
        axioms=[x.strip() for x in matches[0].split(',') if x.strip()]
        assert len(axioms)==len(set(axioms)) and set(required)<=set(axioms),theorem
        assert not any('sorry' in x.lower() for x in axioms)
        if review['status']=='EXACT_AXIOMS_REVIEWED':assert set(axioms)==set(review['exports'][theorem]),theorem
        exports.append({'theorem':theorem,'axioms':axioms,'additional_axioms':sorted(set(axioms)-set(required))})
    assert actual==objects(list(source['sources'])),'Objects changed during collection'
    assert files['job.log']==(job/'log').read_bytes()
    report={'status':'CONDITIONAL_CAPSTONE_ARTIFACT_AUDIT_PASS' if review['status']=='EXACT_AXIOMS_REVIEWED' else 'NEEDS_EXACT_AXIOM_REVIEW',
            'job':job.name,'execution_commit':pin,'authoritative_exit':rc,'results':rows,'exports':exports,
            'audited_reused_objects':len(source['audited_imports']),'new_modules':[m for m in fresh if m in source['sources']],
            'source_review':source['source_review'],'resource_note':source['resource_note'],'scope':source['scope'],
            'unconditional_drop_verified':False,'retained_sha256':{n:sha(b) for n,b in files.items()}}
    print(json.dumps({'audit':report,'files':{n:base64.b64encode(b).decode() for n,b in files.items()}}))
