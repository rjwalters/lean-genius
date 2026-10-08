"""Read-only capture of the corrected plugin evaluation, including failures."""
import base64
import hashlib
import json
from pathlib import Path
import shlex
import subprocess

ROOT = Path(__file__).resolve().parent
CLOUD = r'''
import base64,hashlib,json,pathlib,re,subprocess
job=pathlib.Path('/opt/e85/jobs/20261008T115032-erdos85__h3-triple-formal-20261007-469274')
if not (job/'exit').exists():
    pid=int((job/'pid').read_text())
    print(json.dumps({'status':'PENDING','pid':pid,'pid_exists':pathlib.Path(f'/proc/{pid}').exists()}))
    raise SystemExit(0)
repo=pathlib.Path('/opt/e85/wt/erdos85__h3-triple-formal-20261007')
rel='research/problems/erdos-85-wip-01/h3_precompiled_probe_20261008'
root=repo/rel
files={'job.'+n:(job/n).read_bytes() for n in ('log','spec','exit')}
log=files['job.log'].decode()
commits=re.findall(r'^\[e85\] commit ([0-9a-f]{40}) ',log,re.M)
assert len(commits)==1 and commits[0].startswith('2ca3c3209b3'),commits
for n in ('H3NativeRuntime.lean','H3NativeProbe.lean','SOURCE.json','run_plugin.py'):
    data=subprocess.check_output(['git','-C',str(repo),'show',commits[0]+':'+rel+'/'+n])
    assert data==(root/n).read_bytes(),n
    files[n]=data
attempt=root/'attempt2'
run=json.loads((attempt/'RUN.json').read_text())
files['RUN.json']=(attempt/'RUN.json').read_bytes()
for step in run['steps']:
    name=step['name']+'.log';data=(attempt/name).read_bytes()
    assert hashlib.sha256(data).hexdigest()==step['log_sha256'],name
    files[name]=data
for name,item in run.get('artifacts',{}).items():
    data=(attempt/name).read_bytes()
    assert len(data)==item['bytes'] and hashlib.sha256(data).hexdigest()==item['sha256'],name
exit_code=int(files['job.exit'])
prior=(root/'attempt1/RUN.json').read_bytes()
assert hashlib.sha256(prior).hexdigest()==run['prior_receipt_sha256']
assert prior==(root/'evidence1/RUN.json').read_bytes()
files['baseline.RUN.json']=prior
previous=json.loads(prior)
files['baseline.log']=(root/'attempt1/plain.log').read_bytes()
assert hashlib.sha256(files['baseline.log']).hexdigest()==previous['steps'][2]['log_sha256']
if (attempt/'symbols.log').exists(): files['symbols.log']=(attempt/'symbols.log').read_bytes()
if run['status']=='PLUGIN_COMPILED':
    assert exit_code==0
    assert [s['name'] for s in run['steps']]==['shared','plugin']
    assert all(s['returncode']==0 and not s['timed_out'] for s in run['steps'])
    expected={'propext','Quot.sound','Erdos85.H3TripleCompletion.phaseTwoTraversal._native.native_decide.ax_1_1'}
    for name in ('baseline.log','plugin.log'):
        text=files[name].decode()
        assert 'sorry' not in text.lower() and not re.search(r'\berror:',text,re.I)
        matches=re.findall(r"'Erdos85.H3TripleCompletion.phaseTwoTraversal' depends on axioms: \[([^\]]*)\]",text)
        assert len(matches)==1
        axioms=[a.strip() for a in matches[0].split(',')]
        assert len(axioms)==len(expected) and set(axioms)==expected,axioms
status='COPIED_RUNTIME_PLUGIN_COMPARISON_CAPTURED' if run['status']=='PLUGIN_COMPILED' else 'FAILED_ATTEMPT_CAPTURED'
report={'status':status,'job':job.name,'execution_commit':commits[0],
        'authoritative_exit':exit_code,'run_status':run['status'],
        'retained_sha256':{n:hashlib.sha256(b).hexdigest() for n,b in files.items()},
        'scope':'Standalone copied-runtime timing only; no production exclusion or equivalence credit.'}
assert (job/'log').read_bytes()==files['job.log']
print(json.dumps({'audit':report,'files':{n:base64.b64encode(b).decode() for n,b in files.items()}}))
'''


def main():
    code = 'import base64;exec(compile(base64.b64decode(' + repr(
        base64.b64encode(CLOUD.encode()).decode()) + '),"capture_probe_remote","exec"))'
    result = subprocess.run(['/Users/rwalters/.local/bin/e85-remote', 'ssh',
                             'python3 -B -c ' + shlex.quote(code)], capture_output=True, check=True)
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
    directory = ROOT / 'evidence2'
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
