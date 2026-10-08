"""Read-only audit of the exact production-runtime bucket-zero canary."""
import base64
import hashlib
import json
from pathlib import Path
import shlex
import subprocess

ROOT = Path(__file__).resolve().parent
CLOUD = r'''
import base64,hashlib,json,pathlib,re,subprocess
job=pathlib.Path('/opt/e85/jobs/20261008T120507-erdos85__h3-triple-formal-20261007-479545')
if not (job/'exit').exists():
    pid=int((job/'pid').read_text())
    print(json.dumps({'status':'PENDING','pid':pid,'pid_exists':pathlib.Path(f'/proc/{pid}').exists()}))
    raise SystemExit(0)
repo=pathlib.Path('/opt/e85/wt/erdos85__h3-triple-formal-20261007')
area='research/problems/erdos-85-wip-01/h3_phase3_runtime_20261008'
root=repo/area
attempt=root/'canary1'
def sha(data):return hashlib.sha256(data).hexdigest()
files={'job.'+n:(job/n).read_bytes() for n in ('log','spec','exit')}
log=files['job.log'].decode()
commits=re.findall(r'^\[e85\] commit ([0-9a-f]{40}) ',log,re.M)
assert len(commits)==1 and commits[0].startswith('9739de63467'),commits
for name in ('run_canary.py','build-evidence/AUDIT.json'):
    data=subprocess.check_output(['git','-C',str(repo),'show',commits[0]+':'+area+'/'+name])
    assert data==(root/name).read_bytes(),name
    files[name.replace('/','-')]=data
source=area.replace('h3_phase3_runtime_20261008','h3_triple_completion_20261008')+'/Probe384R0.lean'
files['Probe384R0.lean']=subprocess.check_output(['git','-C',str(repo),'show',commits[0]+':'+source])
assert files['Probe384R0.lean']==(repo/source).read_bytes()
files['RUN.json']=(attempt/'RUN.json').read_bytes()
run=json.loads(files['RUN.json'])
assert sha(files['Probe384R0.lean'])==run['source_sha256']
assert sha(files['build-evidence-AUDIT.json'])==run['build_audit_sha256']
prior=json.loads(files['build-evidence-AUDIT.json'])
assert prior['status']=='RUNTIME_HELPERS_CHAIN_BUILD_AUDIT_PASS'
cache=pathlib.Path('/var/lib/docker/volumes/lean-build-erdos85__h3-triple-formal-20261007/_data')
objects={}
for item in prior['results']:
    module=item['module'];path='proofs/Proofs/'+module+'.lean'
    data=(repo/path).read_bytes()
    assert sha(data)==item['source_sha256']
    assert data==subprocess.check_output(['git','-C',str(repo),'show',commits[0]+':'+path])
    digest=subprocess.check_output(['sudo','sha256sum',str(cache/'lib/lean/Proofs'/(module+'.olean'))],text=True).split()[0]
    assert digest==item['olean_sha256']
    objects[module]=digest
digest=subprocess.check_output(['sudo','sha256sum',str(cache/'ir/Proofs/Erdos85H3TripleCompletionRuntime.c')],text=True).split()[0]
assert digest==prior['runtime_c']['sha256']==run['runtime_c']['sha256']
for step in run['steps']:
    name=step['name']+'.log';data=(attempt/name).read_bytes()
    assert sha(data)==step['log_sha256'],name
    files[name]=data
for name,item in run.get('artifacts',{}).items():
    data=(attempt/name).read_bytes()
    assert len(data)==item['bytes'] and sha(data)==item['sha256'],name
if (attempt/'symbols.log').exists():files['symbols.log']=(attempt/'symbols.log').read_bytes()
rc=int(files['job.exit'])
axioms=[]
if run['status']=='COMPILED':
    assert rc==0 and len(run['steps'])==2
    assert [s['name'] for s in run['steps']]==['shared','probe']
    assert all(s['returncode']==0 and not s['timed_out'] for s in run['steps'])
    assert [s['timeout_seconds'] for s in run['steps']]==[60,180]
    name='Erdos85.H3TripleCompletion.triplePart_384_0'
    text=files['probe.log'].decode()
    assert not re.search(r'\b(sorry|error)\b',text,re.I)
    reports=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",text)
    assert len(reports)==1 and reports[0][0]==name
    axioms=[a.strip() for a in reports[0][1].split(',') if a.strip()]
    assert len(axioms)==3 and set(axioms)=={'propext','Quot.sound',name+'._native.native_decide.ax_1_1'}
    assert run['artifacts']['Probe384R0.olean']['bytes']>0
else:
    assert rc!=0
assert not (repo/'proofs/H3TripleCompletionHelpersProbe.lean').exists()
assert (job/'log').read_bytes()==files['job.log']
report={'status':run['status'],'job':job.name,'execution_commit':commits[0],
        'authoritative_exit':rc,'prerequisite_objects_unchanged':objects,'part_axioms':axioms,
        'retained_sha256':{n:sha(b) for n,b in files.items()},
        'scope':'Reverification of existing bucket 384/0 with production runtime plugin; 383 other premises remain unverified.'}
print(json.dumps({'audit':report,'files':{n:base64.b64encode(b).decode() for n,b in files.items()}}))
'''


def main():
    code = 'import base64;exec(compile(base64.b64decode(' + repr(
        base64.b64encode(CLOUD.encode()).decode()) + '),"capture_canary_remote","exec"))'
    result = subprocess.run(['/Users/rwalters/.local/bin/e85-remote', 'ssh',
                             'python3 -B -c ' + shlex.quote(code)], capture_output=True)
    if result.returncode:
        print(result.stderr.decode(), end='')
        raise SystemExit(result.returncode)
    bundle = json.loads(result.stdout)
    if bundle.get('status') == 'PENDING':
        print(json.dumps(bundle))
        return
    audit = bundle['audit']
    audit['capture_script_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    files = {n: base64.b64decode(b) for n, b in bundle['files'].items()}
    for name, data in files.items():
        assert hashlib.sha256(data).hexdigest() == audit['retained_sha256'][name]
    files['AUDIT.json'] = (json.dumps(audit, indent=2) + '\n').encode()
    directory = ROOT / 'canary-evidence'
    directory.mkdir(exist_ok=True)
    for name, data in files.items():
        path = directory / name
        if path.exists():
            assert path.read_bytes() == data, 'Refusing to overwrite historical evidence: ' + name
        else:
            path.write_bytes(data)
    print(json.dumps(audit, indent=2))
    print(files['RUN.json'].decode())


if __name__ == '__main__':
    main()
