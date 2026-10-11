"""Bounded cloud-only C profiling; no graph-exclusion evidence is produced."""
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import resource
import signal
import subprocess
import time

ROOT = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def limits():
    resource.setrlimit(resource.RLIMIT_AS, (2 * 1024**3, 2 * 1024**3))
    resource.setrlimit(resource.RLIMIT_CPU, (30, 30))


def run(cmd, log):
    started = datetime.now(timezone.utc).isoformat()
    begin = time.monotonic()
    with log.open('xb') as stream:
        p = subprocess.Popen(cmd, stdout=stream, stderr=subprocess.STDOUT,
                             start_new_session=True, preexec_fn=limits)
        try:
            rc = p.wait(timeout=30)
            timed_out = False
        except subprocess.TimeoutExpired:
            os.killpg(p.pid, signal.SIGKILL)
            rc = p.wait()
            timed_out = True
    return {'command': cmd, 'started_utc': started, 'returncode': rc,
            'outer_timeout': timed_out, 'elapsed_seconds': time.monotonic()-begin,
            'log_sha256': sha(log)}


def parse(log):
    text = log.read_text()
    masks = re.findall(r'^T1 core=22 E0=25 patterns=344 masks:(.*)$', text, re.M)
    assert len(masks) == 1
    assert list(map(int, masks[0].split())) == [0,0,0,7]+[1]*7+[2]*7+[4]*7+[0]*24
    lines = re.findall(r'^PROFILE (.*)$', text, re.M)
    assert len(lines) == 1
    fields = dict(re.findall(r'(\w+)=([\d.]+)', lines[0]))
    fields = {k: float(v) if k == 'secs' else int(v) for k,v in fields.items()}
    assert fields['mrv'] == fields['fc'] == fields['n3'] == fields['found'] == 0
    gate = re.findall(r'^GATE enabled=(\d+) hits=(\d+) node_cap=(\d+)$', text, re.M)
    assert len(gate) == 1
    fields.update(zip(('early_gate','gate_hits','node_cap'), map(int,gate[0])))
    return fields


def main():
    assert Path('/opt/e85/jobs').is_dir(), 'Run only on the existing cloud builder'
    assert os.sched_getaffinity(0) == {0,1}
    output = ROOT / 'prototype-degree-gate'
    output.mkdir(exist_ok=False)
    source = ROOT / 'h3_phase2_profile.c'
    binary = output / 'profile'
    report = {'source_sha256': sha(source), 'runner_sha256': sha(Path(__file__)),
              'affinity': sorted(os.sched_getaffinity(0)), 'child_address_space_bytes':2*1024**3,
              'child_cpu_seconds':30, 'child_wall_seconds':30, 'scope':'PROFILING_ONLY', 'runs':{}}
    compile_run = run(['gcc','-O3','-std=gnu11',str(source),'-o',str(binary)], output/'compile.log')
    report['compile'] = compile_run
    assert compile_run['returncode'] == 0
    report['binary_sha256'] = sha(binary)
    common = [str(binary),'1','mrv=0','fc=0','pre=22','mod=384','secs=20','nodes=2000000']
    control = run(common+['res=-1','p1only=1','verbose=1','earlygate=0'], output/'control.log')
    assert control['returncode'] == 0 and not control['outer_timeout']
    control['profile'] = parse(output/'control.log')
    expected = json.loads((ROOT/'profile-fixed-evidence/AUDIT.json').read_text())['profile']
    assert control['profile']['n1'] == expected['nodes']
    assert control['profile']['leaf1'] == expected['leaves']
    assert control['profile']['stopped'] == 0
    vectors = re.findall(r'^((?: \d+){384})$',(output/'control.log').read_text(),re.M)
    assert len(vectors) == 1 and list(map(int,vectors[0].split())) == expected['buckets']
    report['runs']['control'] = control
    for gate in (0,1):
        label = 'baseline' if gate == 0 else 'early-gate'
        result = run(common+['res=0','p1only=0','verbose=1',f'earlygate={gate}'], output/(label+'.log'))
        if not result['outer_timeout']:
            result['profile'] = parse(output/(label+'.log'))
            assert result['returncode'] == (124 if result['profile']['stopped'] else 0)
        report['runs'][label] = result
    (output/'RUN.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2),flush=True)


if __name__ == '__main__':
    main()
