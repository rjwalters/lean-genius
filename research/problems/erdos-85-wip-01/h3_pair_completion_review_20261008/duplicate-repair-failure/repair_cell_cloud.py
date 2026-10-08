"""Cloud-only Cell compilation against read-only native objects; JSON input.

Retains failed producer evidence and a fresh bounded Cell attempt. No Lake build.
"""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import time

REPO = Path('/opt/e85/wt/erdos85__h3-pair-formal-20261008')
JOB = Path('/opt/e85/jobs/20261008T081713-erdos85__h3-pair-formal-20261008-331716')
OLD = 'b3545ac16ae75faa072a66400bedb087544a03bf'
IMAGE = 'sha256:a5ca6c4e3328a1832d5f9b814ab7c1e35616903b3956341962a5b1a96fb6dff6'
VOLUME = 'lean-build-erdos85__h3-pair-formal-20261008'
PARTS = [f'Erdos85H3PairPart{i:02d}' for i in range(24)]


def sha(b):
    return hashlib.sha256(b).hexdigest()


def object_inventory(names):
    code = '''import pathlib,json,hashlib,sys
p=pathlib.Path(sys.argv[1]);o={}
for n in sys.argv[2:]:
 f=p/(n+'.olean');s=f.stat();b=f.read_bytes()
 o[n]={'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b),'mtime':s.st_mtime}
print(json.dumps(o))'''
    root = f'/var/lib/docker/volumes/{VOLUME}/_data/lib/lean/Proofs'
    return json.loads(subprocess.check_output(['sudo', 'python3', '-c', code, root, *names]))


def main():
    b = json.load(sys.stdin)
    assert (JOB / 'exit').read_text().strip() == '1'
    log = (JOB / 'log').read_text()
    assert 'maximum recursion depth has been reached' in log
    assert re.findall(r'^error: Proofs/([^:]+):', log, re.M) == ['Erdos85H3PairCell.lean']
    prior = b['prior']
    dependencies = {r['module']: r for r in prior['results']}
    names = list(dependencies) + PARTS
    objects = object_inventory(names)
    start = datetime.fromisoformat(re.search(r' started (\S+)', log)[1].replace('Z', '+00:00')).timestamp()
    finish = (JOB / 'exit').stat().st_mtime
    for n in names:
        path = 'proofs/Proofs/' + n + '.lean'
        data = (REPO / path).read_bytes()
        assert data == subprocess.check_output(['git', '-C', str(REPO), 'show', OLD + ':' + path])
        assert sha(data) == b['prerequisite_source_sha256'][n]
        if n in PARTS:
            assert len(re.findall(r'\] Built Proofs\.' + n + r' \(', log)) == 1
            assert objects[n]['bytes'] > 0 and start <= objects[n]['mtime'] <= finish
        else:
            assert objects[n]['sha256'] == dependencies[n]['olean_sha256']
            assert sha(data) == dependencies[n]['source_sha256']
    source = b['source'].encode()
    assert sha(source) == b['source_sha256']
    assert 'native_decide' not in re.sub(r'/\-.*?\-/', '', b['source'], flags=re.S)
    assert 'sorry' not in b['source'] and 'maxRecDepth' not in b['source']
    out = Path('/home/ec2-user/h3-pair-cell-repair') / b['commit'][:12]
    out.mkdir(parents=True, exist_ok=False)
    (out / 'Erdos85H3PairCell.lean').write_bytes(source)
    (out / 'INPUT.json').write_text(json.dumps(b, indent=2) + '\n')
    (out / 'repair_cell_cloud.py').write_text(b['runner_source'])
    for n in ['log', 'spec', 'exit']:
        (out / ('producer.' + n)).write_bytes((JOB / n).read_bytes())
    (out / 'PREREQUISITES.json').write_text(json.dumps(objects, indent=2) + '\n')
    name = 'h3-pair-cell-repair-' + b['commit'][:12]
    cmd = ['docker', 'create', '--name', name, '--memory', '16g', '--memory-swap', '16g',
           '--cpus', '2', '--network', 'none', '-v', str(REPO) + ':/workspace:ro',
           '-v', VOLUME + ':/workspace/proofs/.lake/build:ro',
           '-v', 'lean-mathlib-packages:/workspace/proofs/.lake/packages:ro',
           '-v', str(out) + ':/repair:rw', '-w', '/workspace/proofs', IMAGE,
           'lake', 'env', 'lean', '/repair/Erdos85H3PairCell.lean',
           '-o', '/repair/Erdos85H3PairCell.olean']
    subprocess.run(cmd, check=True, capture_output=True)
    (out / 'container-created.json').write_bytes(subprocess.check_output(['docker', 'inspect', name]))
    begun = time.time()
    try:
        process = subprocess.run(['docker', 'start', '-a', name], capture_output=True, timeout=600)
        client_exit = process.returncode
    except subprocess.TimeoutExpired:
        subprocess.run(['docker', 'kill', name], check=True, capture_output=True)
        subprocess.run(['docker', 'wait', name], check=True, capture_output=True)
        client_exit = 124
    inspection = subprocess.check_output(['docker', 'inspect', name])
    state = json.loads(inspection)[0]['State']
    assert state['Running'] is False
    (out / 'container-terminal.json').write_bytes(inspection)
    logs = subprocess.run(['docker', 'logs', name], capture_output=True, check=True)
    (out / 'lean.stdout').write_bytes(logs.stdout)
    (out / 'lean.stderr').write_bytes(logs.stderr)
    obj = out / 'Erdos85H3PairCell.olean'
    result = {'status': 'CELL_REPAIR_COMPILED' if state['ExitCode'] == client_exit == 0 else 'CELL_REPAIR_FAILED',
              'commit': b['commit'], 'source_sha256': sha(source), 'producer_job': JOB.name,
              'producer_exit': 1, 'completed_parts': 24, 'command': cmd,
              'container_exit': state['ExitCode'], 'client_exit': client_exit,
              'started_epoch': begun, 'finished_epoch': time.time(),
              'olean_sha256': sha(obj.read_bytes()) if obj.exists() else None,
              'prerequisites_unchanged': object_inventory(names) == objects}
    assert result['prerequisites_unchanged']
    (out / 'RUN.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'output': str(out), 'result': result, 'stdout': logs.stdout.decode(), 'stderr': logs.stderr.decode()}))


if __name__ == '__main__':
    main()
