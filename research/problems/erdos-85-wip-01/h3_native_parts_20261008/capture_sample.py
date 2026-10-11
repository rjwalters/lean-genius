"""Independently accept completed sample parts from an explicitly pinned job."""
import argparse
import base64
import hashlib
import json
from pathlib import Path
import re
import shlex
import subprocess

ROOT = Path(__file__).resolve().parent
CLOUD = r'''
import base64,hashlib,json,pathlib,re,subprocess
from datetime import datetime
def sha(data):return hashlib.sha256(data).hexdigest()
repo=pathlib.Path('/opt/e85/wt/erdos85__h3-triple-formal-20261007')
area='research/problems/erdos-85-wip-01/h3_native_parts_20261008'
root=repo/area;attempt=root/'sample1'
job=pathlib.Path('/opt/e85/jobs')/CONFIG['job']
if not (job/'exit').exists():
    pid=int((job/'pid').read_text())
    print(json.dumps({'status':'PENDING','job':job.name,'pid':pid,
                      'pid_exists':pathlib.Path(f'/proc/{pid}').exists()}))
    raise SystemExit(0)
files={'job.'+n:(job/n).read_bytes() for n in ('log','spec','exit')}
log=files['job.log'].decode();rc=int(files['job.exit'])
assert re.findall(r'^\[e85\] commit ([0-9a-f]{40}) ',log,re.M)==[CONFIG['commit']]
for name in ('MANIFEST.json','prepare.py','run_sample.py'):
    data=subprocess.check_output(['git','-C',str(repo),'show',CONFIG['commit']+':'+area+'/'+name])
    assert data==(root/name).read_bytes(),name
    files[name]=data
m=json.loads(files['MANIFEST.json'])
assert sha(files['prepare.py'])==m['source_generator_sha256']
assert m['sizing_sample']['residues_in_order']==[0,3,5,4,162]
assert [p['residue'] for p in m['parts']]==list(range(384))
assert len({p['module'] for p in m['parts']})==384
files['RUN.json']=(attempt/'RUN.json').read_bytes()
run=json.loads(files['RUN.json'])
assert run['manifest_sha256']==sha(files['MANIFEST.json'])
assert run['cgroup_memory_bytes']==16*1024**3
quota,period=map(int,run['cgroup_cpu_max'].split());assert quota==2*period
spec=files['job.spec'].decode()
for line in ('MEM_GB=16','TIMEOUT=10m','THREADS=1','CPUS=2','FULL=1'):
    assert line in spec.splitlines(),line
audit_data=(repo/m['prerequisite_audit']['path']).read_bytes()
assert sha(audit_data)==m['prerequisite_audit']['sha256']==run['prerequisite_audit_sha256']
files['prerequisite-AUDIT.json']=audit_data
prior=json.loads(audit_data)
cache=pathlib.Path('/var/lib/docker/volumes/lean-build-erdos85__h3-triple-formal-20261007/_data')
for item in prior['results']:
    path='proofs/Proofs/'+item['module']+'.lean'
    data=(repo/path).read_bytes()
    assert sha(data)==item['source_sha256']
    assert data==subprocess.check_output(['git','-C',str(repo),'show',CONFIG['commit']+':'+path])
    actual=subprocess.check_output(['sudo','sha256sum',str(cache/'lib/lean/Proofs'/(item['module']+'.olean'))],text=True).split()[0]
    assert actual==item['olean_sha256']
actual=subprocess.check_output(['sudo','sha256sum',str(cache/'ir/Proofs/Erdos85H3TripleCompletionRuntime.c')],text=True).split()[0]
assert actual==prior['runtime_c']['sha256']
if 'library' in run:
    data=(attempt/'libH3TripleRuntime.so').read_bytes()
    assert sha(data)==run['library']['sha256'] and len(data)==run['library']['bytes']
steps={s['name']:s for s in run['steps']}
assert len(steps)==len(run['steps'])
for name,s in steps.items():
    files[name+'.log']=(attempt/(name+'.log')).read_bytes()
    assert sha(files[name+'.log'])==s['log_sha256']
    assert s['timeout_seconds']==(60 if name=='shared' else 90)
    assert 0<s['effective_timeout_seconds']<=s['timeout_seconds']
residues=[p['residue'] for p in run['parts']]
assert residues==m['sizing_sample']['residues_in_order'][:len(residues)]
start=datetime.fromisoformat(run['started_utc']).timestamp()
finish=(job/'exit').stat().st_mtime
accepted=[]
for item in run['parts']:
    r=item['residue'];row=m['parts'][r];step=steps[f'part{r:03d}']
    source=(attempt/'sources'/row['source_path']).read_bytes()
    assert sha(source)==row['source_sha256']==item['source_sha256']
    assert source==(root/'source-review'/row['source_path']).read_bytes()
    files['sources/'+row['source_path']]=source
    assert not (repo/'proofs'/row['source_path']).exists()
    assert step['command']==['lean','-j1',
        '--plugin=/workspace/'+area+'/sample1/libH3TripleRuntime.so='+run['initializer'],
        row['source_path'],'-o','/workspace/proofs/.lake/build/lib/lean/Proofs/'+row['module'].split('.')[-1]+'.olean']
    if item['status']!='COMPILED_PENDING_AUDIT':
        assert item is run['parts'][-1] and step['returncode']!=0
        continue
    assert step['returncode']==0 and not step['timed_out']
    raw=files[f'part{r:03d}.log'].decode()
    assert not re.search(r'\b(sorry|error)\b',raw,re.I)
    matches=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",raw)
    assert len(matches)==1 and matches[0][0]==row['theorem']
    axioms=[a.strip() for a in matches[0][1].split(',') if a.strip()]
    assert len(axioms)==3 and set(axioms)=={'propext','Quot.sound',row['native_axiom']}
    obj=attempt/'objects'/(row['module'].split('.')[-1]+'.olean')
    data=obj.read_bytes()
    assert len(data)==item['object_bytes']>0 and sha(data)==item['object_sha256']
    assert start<=item['object_mtime']<=finish
    script='import pathlib,hashlib,json,sys;p=pathlib.Path(sys.argv[1]);s=p.stat();print(json.dumps({"sha256":hashlib.sha256(p.read_bytes()).hexdigest(),"bytes":s.st_size,"mtime":s.st_mtime}))'
    actual=json.loads(subprocess.check_output(['sudo','python3','-c',script,str(cache/'lib/lean/Proofs'/obj.name)]))
    assert actual['sha256']==item['object_sha256'] and actual['bytes']==item['object_bytes']
    assert actual['mtime']==item['object_mtime'] and start<=actual['mtime']<=finish
    accepted.append({'residue':r,'module':row['module'],'theorem':row['theorem'],
                     'axioms':axioms,'source_sha256':sha(source),'object_sha256':sha(data),
                     'object_bytes':len(data),'elapsed_seconds':step['elapsed_seconds'],
                     'child_user_seconds':step['child_user_seconds']})
if rc==0:
    assert run['status']=='SAMPLE_COMPILED_PENDING_AUDIT' and [p['residue'] for p in accepted]==[0,3,5,4,162]
else:
    assert run['status'] in ('STOPPED','TIMEOUT','ALARM','COMPILE_TIMEOUT')
assert (job/'log').read_bytes()==files['job.log']
report={'status':'SAMPLE_ARTIFACT_AUDIT_PASS' if rc==0 else 'PARTIAL_SAMPLE_ARTIFACT_AUDIT',
        'job':job.name,'execution_commit':CONFIG['commit'],'authoritative_exit':rc,
        'worker_status':run['status'],'accepted_parts':accepted,
        'retained_sha256':{n:sha(b) for n,b in files.items()},
        'scope':'Only listed accepted parts; no full 384-part or whole-cell verdict. Bucket zero replaces diagnostic packaging, not an additional residue.'}
print(json.dumps({'audit':report,'files':{n:base64.b64encode(b).decode() for n,b in files.items()}}))
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--job', required=True)
    parser.add_argument('--commit', required=True)
    args = parser.parse_args()
    assert re.fullmatch(r'\d{8}T\d{6}-erdos85__h3-triple-formal-20261007-\d+', args.job)
    assert re.fullmatch(r'[0-9a-f]{40}', args.commit)
    code = 'CONFIG=' + repr(vars(args)) + '\n' + CLOUD
    remote = 'import base64;exec(compile(base64.b64decode(' + repr(
        base64.b64encode(code.encode()).decode()) + '),"sample_audit","exec"))'
    result = subprocess.run(['/Users/rwalters/.local/bin/e85-remote', 'ssh',
                             'python3 -B -c ' + shlex.quote(remote)], capture_output=True)
    if result.returncode:
        print(result.stderr.decode(), end='')
        raise SystemExit(result.returncode)
    bundle = json.loads(result.stdout)
    if bundle.get('status') == 'PENDING':
        print(json.dumps(bundle))
        return
    audit = bundle['audit']
    audit['collector_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    files = {n: base64.b64decode(b) for n, b in bundle['files'].items()}
    for name, data in files.items():
        assert hashlib.sha256(data).hexdigest() == audit['retained_sha256'][name]
    files['AUDIT.json'] = (json.dumps(audit, indent=2) + '\n').encode()
    for name, data in files.items():
        path = ROOT / 'sample-evidence' / name
        path.parent.mkdir(parents=True, exist_ok=True)
        if path.exists():
            assert path.read_bytes() == data, 'Refusing to overwrite historical evidence: ' + name
        else:
            path.write_bytes(data)
    print(audit['status'])
    print(json.dumps(audit['accepted_parts'], indent=2))


if __name__ == '__main__':
    main()
