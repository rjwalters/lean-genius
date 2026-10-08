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
job = Path('/opt/e85/jobs/20261008T103524-erdos85__h3-triple-formal-20261007-417821')
commit = '4ac20ada301d806426214fd80d4eec0b8fcb722e'
def sha(data): return hashlib.sha256(data).hexdigest()
assert (job / 'exit').exists(), 'Job is not terminal'
rc = int((job / 'exit').read_text())
log = (job / 'log').read_text()
assert re.findall(r'^\[e85\] commit ([0-9a-f]{40}) ', log, re.M) == [commit]
files = {'job.'+n: (job/n).read_bytes() for n in ('log','spec','exit')}
for name in ('PhaseOneProfile.lean','run_profile.py'):
    data = (root/name).read_bytes()
    assert data == subprocess.check_output(['git','-C',str(repo),'show',commit+':'+area+'/'+name])
    files[name] = data
run = json.loads((root/'phase-one-profile/RUN.json').read_bytes())
assert run['source_sha256'] == sha(files['PhaseOneProfile.lean'])
assert run['timeout_seconds'] == 60
for name in ('RUN.json','probe.log'):
    files[name] = (root/'phase-one-profile'/name).read_bytes()
assert sha(files['probe.log']) == run['log_sha256']
cache = Path('/var/lib/docker/volumes/lean-build-erdos85__h3-triple-formal-20261007/_data/lib/lean/Proofs')
objects = {}
for item in run['prerequisites']:
    name = item['module']
    assert sha((repo/'proofs/Proofs'/(name+'.lean')).read_bytes()) == item['source_sha256']
    digest = subprocess.check_output(['sudo','sha256sum',str(cache/(name+'.olean'))],text=True).split()[0]
    assert digest == item['olean_sha256']
    objects[name] = digest
obj = root/'phase-one-profile/PhaseOneProfile.olean'
if run['status'] == 'COMPILED':
    assert rc == run['returncode'] == 0 and not run['timed_out']
    assert obj.stat().st_size == run['olean_bytes'] > 0
    assert sha(obj.read_bytes()) == run['olean_sha256']
    text = files['probe.log'].decode()
    assert not re.search(r'\b(sorry|error)\b', text, re.I)
    counts = re.findall(r'nodes=(\d+) leaves=(\d+) exhausted=(\d+) invalid=(\d+)',text)
    buckets = re.findall(r'buckets=(\[[^\]]+\])',text)
    assert len(counts) == len(buckets) == 1
    nodes,leaves,exhausted,invalid = map(int,counts[0])
    buckets = json.loads(buckets[0])
    assert nodes > 0 and leaves > 0 and exhausted == invalid == 0
    assert len(buckets) == 384 and all(type(x) is int and x >= 0 for x in buckets)
    assert sum(buckets) == leaves
    profile = {'nodes':nodes,'leaves':leaves,'exhausted':exhausted,'invalid':invalid,
               'buckets':buckets,'bucket0':buckets[0],'minimum':min(buckets),'maximum':max(buckets)}
elif run['status'] == 'TIMEOUT':
    # docker-build.sh maps the command's exit 124 to wrapper exit 1.
    assert rc == 1 and run['timed_out'] and run['returncode'] == -9 and not obj.exists()
    assert '=== Build timed out after 2m ===' in log
    assert 60 <= run['elapsed_seconds'] < 120
else:
    assert run['status'] == 'FAILED' and rc != 0 and run['returncode'] != 0
assert not (repo/'proofs/H3TripleCompletionPhaseOneProfile.lean').exists()
report = {'job':job.name,'execution_commit':commit,'status':run['status'],
          'exit':rc,'prerequisite_objects_unchanged':objects,
          'retained_sha256':{k:sha(v) for k,v in files.items()},
          'scope':'Instrumented phase-one traversal/hash profile only; no theorem or graph-exclusion credit.'}
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
        path = ROOT/'profile-evidence'/name
        path.parent.mkdir(parents=True,exist_ok=True)
        if path.exists():
            assert path.read_bytes() == data, 'Refusing to overwrite historical bytes: '+name
        else:
            path.write_bytes(data)
    print(json.dumps(report,indent=2))


if __name__ == '__main__':
    main()
