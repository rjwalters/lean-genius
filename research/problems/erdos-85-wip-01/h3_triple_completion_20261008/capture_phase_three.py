"""Retain and check the terminal C comparison without running it again."""
import base64
import hashlib
import json
from pathlib import Path
import shlex
import subprocess

ROOT = Path(__file__).resolve().parent
CLOUD = r'''
import base64,hashlib,json,re,subprocess
from pathlib import Path
repo=Path('/opt/e85/wt/erdos85__h3-triple-formal-20261007')
area='research/problems/erdos-85-wip-01/h3_triple_completion_20261008'
root=repo/area
out=root/'prototype-phase-three'
job=Path('/opt/e85/jobs/20261008T112128-erdos85__h3-triple-formal-20261007-450887')
pin='0779d10cba3a4a9b13feb5634cb15f55ddc4b4bf'
def sha(data):return hashlib.sha256(data).hexdigest()
assert (job/'exit').read_text().strip()=='0'
raw=(job/'log').read_bytes()
assert re.findall(r'^\[e85\] commit ([0-9a-f]{40}) ',raw.decode(),re.M)==[pin]
files={'job.'+n:(job/n).read_bytes() for n in ('log','spec','exit')}
for name in ('h3_phase3_profile.c','run_phase_three.py','run_prototype.py'):
    data=(root/name).read_bytes()
    assert data==subprocess.check_output(['git','-C',str(repo),'show',pin+':'+area+'/'+name])
    files[name]=data
for name in ('RUN.json','compile.log','control.log','phase-two.log','phase-three.log'):
    files[name]=(out/name).read_bytes()
run=json.loads(files['RUN.json'])
for name,digest in run['source_hashes'].items():
    assert sha(files[name])==digest
assert sha((out/'profile').read_bytes())==run['binary_sha256']
assert run['affinity']==[0,1] and run['child_address_space_bytes']==2*1024**3
assert run['compile']['returncode']==0
assert sha(files['compile.log'])==run['compile']['log_sha256']
expected=json.loads((root/'profile-fixed-evidence/AUDIT.json').read_text())['profile']
vectors=re.findall(r'^((?: \d+){384})$',files['control.log'].decode(),re.M)
assert len(vectors)==1 and list(map(int,vectors[0].split()))==expected['buckets']
for label,record in run['runs'].items():
    assert not record['outer_timeout']
    data=files[label+'.log'];assert sha(data)==record['log_sha256']
    line=re.findall(r'^PROFILE (.*)$',data.decode(),re.M);assert len(line)==1
    fields=dict(re.findall(r'(\w+)=([\d.]+)',line[0]))
    for key,value in fields.items():
        assert (float(value) if key=='secs' else int(value))==record['profile'][key]
    assert record['profile']['found']==0
    if label!='phase-three': assert record['profile']['n3']==0
    if label=='control':
        assert record['returncode']==0 and record['profile']['stopped']==0
        assert record['profile']['n1']==expected['nodes'] and record['profile']['leaf1']==expected['leaves']
    else:
        assert record['returncode']==0 and record['profile']['stopped']==0
        assert record['profile']['stop_reason']=='none'
        assert record['profile']['leaf1']==record['profile']['leafrun']==4
        assert record['profile']['n1']+record['profile']['n2']+record['profile']['n3']<2000000
        assert record['profile']['n2']==458244 and record['profile']['leaf2']==19920
        assert record['profile']['states']==[[1,975744,1393],[2,986112,6289],[3,41088,6321],[4,776448,7657]]
    full=re.findall(r'^FULL p3=(\d+) gates=(\d+) combinations=(\d+) rejects=(\d+)$',data.decode(),re.M)
    assert len(full)==1
    for key,value in zip(('p3','p3_gates','p3_combinations','p3_rejects'),map(int,full[0])):
        assert record['profile'][key]==value
    assert record['profile']['p3']==(1 if label=='phase-three' else 0)
    assert not record['profile']['candidates'] and 'CANDIDATE' not in data.decode()
    if label=='phase-three':
        p=record['profile']
        assert p['n3']==24322 and p['p3_gates']==4141
        assert p['p3_combinations']==52876 and p['p3_rejects']==48474
        assert p['n3']==p['leaf2']+p['p3_combinations']-p['p3_rejects']
    order=re.findall(r'^ORDER pick=(\d+) stop_reason=(\S+) maxleaf=(\d+)$',data.decode(),re.M)
    assert len(order)==1
    pick,reason,maxleaf=order[0]
    assert int(pick)==record['profile']['pick'] and reason==record['profile']['stop_reason']
    assert int(maxleaf)==record['profile']['maxleaf']
    states=[list(map(int,x)) for x in re.findall(r'^STATE leaf=(\d+) key=(\d+) n1=(\d+)$',data.decode(),re.M)]
    assert states==record['profile']['states']
    assert record['profile']['early_gate']==0
report={'status':'PHASE_THREE_PROTOTYPE_AUDIT_PASS','job':job.name,'execution_commit':pin,
        'binary_sha256':run['binary_sha256'],'source_hashes':run['source_hashes'],
        'runs':run['runs'],'retained_sha256':{k:sha(v) for k,v in files.items()},
        'scope':'C profiling only; complete bucket-zero three-phase prototype traversal, no formal exclusion credit.'}
print(json.dumps({'report':report,'files':{k:base64.b64encode(v).decode() for k,v in files.items()}}))
'''


def main():
    code = ('import base64;exec(compile(base64.b64decode('
            + repr(base64.b64encode(CLOUD.encode()).decode()) + '),"audit_prototype","exec"))')
    result = subprocess.run(['/Users/rwalters/.local/bin/e85-remote','ssh',
                             'python3 -B -c '+shlex.quote(code)],capture_output=True)
    if result.returncode:
        raise RuntimeError(result.stderr.decode())
    bundle=json.loads(result.stdout)
    report=bundle['report']
    report['auditor_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    files={name:base64.b64decode(value) for name,value in bundle['files'].items()}
    for name,data in files.items():
        assert hashlib.sha256(data).hexdigest()==report['retained_sha256'][name]
    files['AUDIT.json']=(json.dumps(report,indent=2)+'\n').encode()
    for name,data in files.items():
        path=ROOT/'phase-three-evidence'/name
        path.parent.mkdir(parents=True,exist_ok=True)
        if path.exists():
            assert path.read_bytes()==data,'Refusing to overwrite evidence: '+name
        else:
            path.write_bytes(data)
    print(report['status'])
    for label,record in report['runs'].items():
        print(label,record['elapsed_seconds'],record['profile'])


if __name__=='__main__':
    main()
