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
job = Path('/opt/e85/jobs/20261008T101712-erdos85__h3-triple-formal-20261007-405471')
commit = '0be06607d7d5e176fa0c8f3abf040d191d4447ee'
def sha(data): return hashlib.sha256(data).hexdigest()
assert (job / 'exit').exists(), 'Job is not terminal'
rc = int((job / 'exit').read_text())
log = (job / 'log').read_text()
assert re.findall(r'^\[e85\] commit ([0-9a-f]{40}) ', log, re.M) == [commit]
files = {'job.'+n: (job/n).read_bytes() for n in ('log','spec','exit')}
for name in ('Probe384R0.lean','run_probe.py'):
    data = (root/name).read_bytes()
    assert data == subprocess.check_output(['git','-C',str(repo),'show',commit+':'+area+'/'+name])
    files[name] = data
run = json.loads((root/'probe384r0/RUN.json').read_bytes())
assert run['source_sha256'] == sha(files['Probe384R0.lean'])
assert run['timeout_seconds'] == 300
for name in ('RUN.json','probe.log'):
    files[name] = (root/'probe384r0'/name).read_bytes()
assert sha(files['probe.log']) == run['log_sha256']
cache = Path('/var/lib/docker/volumes/lean-build-erdos85__h3-triple-formal-20261007/_data/lib/lean/Proofs')
objects = {}
for item in run['prerequisites']:
    name = item['module']
    assert sha((repo/'proofs/Proofs'/(name+'.lean')).read_bytes()) == item['source_sha256']
    digest = subprocess.check_output(['sudo','sha256sum',str(cache/(name+'.olean'))],text=True).split()[0]
    assert digest == item['olean_sha256']
    objects[name] = digest
obj = root/'probe384r0/Probe384R0.olean'
if run['status'] == 'COMPILED':
    assert rc == run['returncode'] == 0 and not run['timed_out']
    assert obj.stat().st_size == run['olean_bytes'] > 0
    assert sha(obj.read_bytes()) == run['olean_sha256']
    text = files['probe.log'].decode()
    assert not re.search(r'\b(sorry|error)\b', text, re.I)
    name = 'Erdos85.H3TripleCompletion.triplePart_384_0'
    reports = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",text)
    assert len(reports) == 1 and reports[0][0] == name
    assert reports[0][1].strip() == name+'._native.native_decide.ax_1_1'
elif run['status'] == 'TIMEOUT':
    # docker-build.sh maps the command's exit 124 to wrapper exit 1.
    assert rc == 1 and run['timed_out'] and run['returncode'] == -9 and not obj.exists()
    assert '=== Build timed out after 6m ===' in log
    assert 300 <= run['elapsed_seconds'] < 360
else:
    assert run['status'] == 'FAILED' and rc != 0 and run['returncode'] != 0
assert not (repo/'proofs/H3TripleCompletionProbe384R0.lean').exists()
report = {'job':job.name,'execution_commit':commit,'status':run['status'],
          'exit':rc,'prerequisite_objects_unchanged':objects,
          'retained_sha256':{k:sha(v) for k,v in files.items()},
          'scope':'One part of 384 only; no whole-cell exclusion or full-campaign estimate.'}
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
    report['container_snapshot_sha256'] = hashlib.sha256((ROOT/'probe-container-live.json').read_bytes()).hexdigest()
    files = {name:base64.b64decode(value) for name,value in bundle['files'].items()}
    for name,data in files.items():
        assert hashlib.sha256(data).hexdigest() == report['retained_sha256'][name]
    files['AUDIT.json'] = (json.dumps(report,indent=2)+'\n').encode()
    for name,data in files.items():
        path = ROOT/'probe-evidence'/name
        path.parent.mkdir(parents=True,exist_ok=True)
        if path.exists():
            assert path.read_bytes() == data, 'Refusing to overwrite historical bytes: '+name
        else:
            path.write_bytes(data)
    print(json.dumps(report,indent=2))


if __name__ == '__main__':
    main()
