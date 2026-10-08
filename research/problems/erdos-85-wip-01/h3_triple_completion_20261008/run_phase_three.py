"""Bounded C all-phase bucket-zero sizing; no formal exclusion evidence."""
import json
import os
from pathlib import Path
import re
from run_prototype import run, sha


ROOT = Path(__file__).resolve().parent


def details(log):
    text = log.read_text()
    masks = re.findall(r'^T1 core=22 E0=25 patterns=344 masks:(.*)$', text, re.M)
    assert len(masks)==1
    assert list(map(int,masks[0].split()))==[0,0,0,7]+[1]*7+[2]*7+[4]*7+[0]*24
    lines=re.findall(r'^PROFILE (.*)$',text,re.M)
    assert len(lines)==1
    p={k:(float(v) if k=='secs' else int(v)) for k,v in re.findall(r'(\w+)=([\d.]+)',lines[0])}
    assert p['mrv']==p['fc']==0
    order=re.findall(r'^ORDER pick=(\d+) stop_reason=(\S+) maxleaf=(\d+)$',text,re.M)
    assert len(order)==1
    p.update(pick=int(order[0][0]),stop_reason=order[0][1],maxleaf=int(order[0][2]))
    p['states']=[list(map(int,row)) for row in re.findall(r'^STATE leaf=(\d+) key=(\d+) n1=(\d+)$',text,re.M)]
    gate=re.findall(r'^GATE enabled=(\d+) hits=(\d+) node_cap=(\d+)$',text,re.M)
    assert len(gate)==1
    p.update(zip(('early_gate','gate_hits','node_cap'),map(int,gate[0])))
    full=re.findall(r'^FULL p3=(\d+) gates=(\d+) combinations=(\d+) rejects=(\d+)$',text,re.M)
    assert len(full)==1
    p.update(zip(('p3','p3_gates','p3_combinations','p3_rejects'),map(int,full[0])))
    assert p['early_gate']==0
    p['candidates']=[list(map(int,row.split())) for row in re.findall(r'^CANDIDATE rows:(.*)$',text,re.M)]
    assert len(p['candidates'])==p['found']
    return p


def main():
    assert Path('/opt/e85/jobs').is_dir()
    assert os.sched_getaffinity(0) == {0, 1}
    output = ROOT/'prototype-phase-three'
    output.mkdir(exist_ok=False)
    source = ROOT/'h3_phase3_profile.c'
    binary = output/'profile'
    names = ['h3_phase3_profile.c', 'run_phase_three.py',
             'run_prototype.py']
    report = {'source_hashes': {n: sha(ROOT/n) for n in names}, 'scope': 'PROFILING_ONLY',
              'affinity': sorted(os.sched_getaffinity(0)), 'child_address_space_bytes': 2*1024**3,
              'child_cpu_seconds': 30, 'child_wall_seconds': 30, 'runs': {}}
    report['compile'] = run(['gcc', '-O3', '-std=gnu11', str(source), '-o', str(binary)],
                            output/'compile.log')
    assert report['compile']['returncode'] == 0
    report['binary_sha256'] = sha(binary)
    common = [str(binary), '1', 'mrv=0', 'fc=0', 'pre=22', 'mod=384',
              'secs=20', 'nodes=2000000', 'earlygate=0', 'verbose=1', 'pick=2']
    for label, args in [('control', ['res=-1', 'p1only=1', 'p3=0']),
                        ('phase-two', ['res=0', 'p1only=0', 'maxleaf=0', 'p3=0']),
                        ('phase-three', ['res=0', 'p1only=0', 'maxleaf=0', 'p3=1'])]:
        result = run(common+args, output/(label+'.log'))
        if not result['outer_timeout']:
            result['profile'] = details(output/(label+'.log'))
            p = result['profile']
            assert result['returncode'] == (124 if p['stopped'] else 0)
            assert p['pick'] == 2 and p['maxleaf'] == 0
            if label == 'control':
                expected = json.loads((ROOT/'profile-fixed-evidence/AUDIT.json').read_text())['profile']
                assert not p['stopped'] and p['n1'] == expected['nodes']
                assert p['leaf1'] == expected['leaves']
                vectors = re.findall(r'^((?: \d+){384})$', (output/'control.log').read_text(), re.M)
                assert len(vectors) == 1 and list(map(int, vectors[0].split())) == expected['buckets']
            else:
                assert p['stop_reason'] in ('none', 'nodes', 'time')
                keys = [row[1] for row in p['states']]
                assert keys == [975744, 986112, 41088, 776448][:len(keys)]
                if not p['stopped'] and not p['found']:
                    assert p['leaf1'] == p['leafrun'] == 4 and p['n1'] == 8167
            if label=='phase-two':
                assert not p['stopped'] and p['found']==p['n3']==0
                assert p['n2']==458244 and p['leaf2']==19920
            assert p['p3']==(1 if label=='phase-three' else 0)
        report['runs'][label] = result
    (output/'RUN.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2), flush=True)


if __name__ == '__main__':
    main()
