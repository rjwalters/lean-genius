"""Read terminal cloud evidence without rerunning the diagnostic."""
import base64
import hashlib
import json
from pathlib import Path
import shlex
import subprocess

ROOT = Path(__file__).resolve().parent
CLOUD = r'''
import base64, hashlib, json, re, subprocess
from pathlib import Path
repo = Path('/opt/e85/wt/erdos85__h3-triple-formal-20261007')
area = 'research/problems/erdos-85-wip-01/h3_triple_completion_20261008'
root = repo / area
job = Path('/opt/e85/jobs/20261008T111445-erdos85__h3-triple-formal-20261007-445375')
commit = 'd02fb5b5430ff42a1113172df00ef16cefc3adaf'
def sha(data): return hashlib.sha256(data).hexdigest()
assert (job / 'exit').exists(), 'Job is not terminal'
rc = int((job / 'exit').read_text())
log = (job / 'log').read_text()
assert re.findall(r'^\[e85\] commit ([0-9a-f]{40}) ', log, re.M) == [commit]
files = {'job.'+n: (job/n).read_bytes() for n in ('log','spec','exit')}
for name in ('PhaseTwoPaired.lean','run_phase_two_paired.py'):
    data = (root/name).read_bytes()
    assert data == subprocess.check_output(['git','-C',str(repo),'show',commit+':'+area+'/'+name])
    files[name] = data
run = json.loads((root/'phase-two-paired/RUN.json').read_bytes())
assert run['source_sha256'] == sha(files['PhaseTwoPaired.lean'])
assert run['timeout_seconds'] == 60
for name in ('RUN.json','probe.log'):
    files[name] = (root/'phase-two-paired'/name).read_bytes()
assert sha(files['probe.log']) == run['log_sha256']
cache = Path('/var/lib/docker/volumes/lean-build-erdos85__h3-triple-formal-20261007/_data/lib/lean/Proofs')
objects = {}
for item in run['prerequisites']:
    name = item['module']
    assert sha((repo/'proofs/Proofs'/(name+'.lean')).read_bytes()) == item['source_sha256']
    digest = subprocess.check_output(['sudo','sha256sum',str(cache/(name+'.olean'))],text=True).split()[0]
    assert digest == item['olean_sha256']
    objects[name] = digest
obj = root/'phase-two-paired/PhaseTwoPaired.olean'
if run['status'] == 'COMPILED':
    assert rc == run['returncode'] == 0 and not run['timed_out']
    assert obj.stat().st_size == run['olean_bytes'] > 0
    assert sha(obj.read_bytes()) == run['olean_sha256']
    text = files['probe.log'].decode()
    assert not re.search(r'\b(sorry|error)\b', text, re.I)
    assert re.findall(r'^STATES count=(\d+)$',text,re.M)==['4']
    rows = re.findall(r'^PROFILE (.*)$',text,re.M)
    assert len(rows)==8
    profiles={'false':[],'true':[]}
    for row in rows:
        pairs=dict(re.findall(r'(\w+)=(\w+)',row))
        assert pairs['capped'] in ('true','false') and pairs['fast'] in profiles
        mode=pairs.pop('fast')
        p={k:(v=='true' if k=='capped' else int(v)) for k,v in pairs.items()}
        assert set(p)=={'leaf','key','nodes','leaves','exhausted','invalid','no_fresh',
                        'rejected','available','capped','elapsed_ms'}
        assert p['leaf']==len(profiles[mode])+1 and 0 < p['nodes'] <= 10000
        assert p['invalid']==p['exhausted']==0
        assert not p['capped'] or p['nodes']==10000
        profiles[mode].append(p)
    expected=json.loads((root/'phase-two-profile-fixed-evidence/AUDIT.json').read_text())['profile']['states']
    for mode,states in profiles.items():
        assert len(states)==4
        for actual,old in zip(states,expected):
            assert {k:v for k,v in actual.items() if k!='elapsed_ms'}=={k:v for k,v in old.items() if k!='elapsed_ms'}
    profile={'modes':profiles,'scope':'Paired instrumented traversal, 10000-node cap per state.'}
elif run['status'] == 'TIMEOUT':
    # docker-build.sh maps the command's exit 124 to wrapper exit 1.
    assert rc == 1 and run['timed_out'] and run['returncode'] == -9 and not obj.exists()
    assert '=== Build timed out after 2m ===' in log
    assert 60 <= run['elapsed_seconds'] < 120
else:
    assert run['status'] == 'FAILED' and rc != 0 and run['returncode'] != 0
assert not (repo/'proofs/H3TripleCompletionPhaseTwoPaired.lean').exists()
report = {'job':job.name,'execution_commit':commit,'status':run['status'],
          'exit':rc,'prerequisite_objects_unchanged':objects,
          'retained_sha256':{k:sha(v) for k,v in files.items()},
          'scope':'Bounded instrumented phase-two profile only; no theorem or graph-exclusion credit.'}
if run['status'] == 'COMPILED': report['profile'] = profile
print(json.dumps({'report':report,'files':{k:base64.b64encode(v).decode() for k,v in files.items()}}))
'''


def main():
    code = ('import base64;exec(compile(base64.b64decode('
            + repr(base64.b64encode(CLOUD.encode()).decode()) + '),"audit_probe","exec"))')
    result = subprocess.run(
        ['/Users/rwalters/.local/bin/e85-remote', 'ssh', 'python3 -B -c ' + shlex.quote(code)],
        capture_output=True)
    if result.returncode:
        raise RuntimeError(result.stderr.decode())
    bundle = json.loads(result.stdout)
    report = bundle['report']
    report['auditor_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    files = {name:base64.b64decode(value) for name,value in bundle['files'].items()}
    for name,data in files.items():
        assert hashlib.sha256(data).hexdigest() == report['retained_sha256'][name]
    files['AUDIT.json'] = (json.dumps(report,indent=2)+'\n').encode()
    for name,data in files.items():
        path = ROOT/'phase-two-paired-evidence'/name
        path.parent.mkdir(parents=True,exist_ok=True)
        if path.exists():
            assert path.read_bytes() == data, 'Refusing to overwrite historical bytes: '+name
        else:
            path.write_bytes(data)
    print(json.dumps(report,indent=2))


if __name__ == '__main__':
    main()
