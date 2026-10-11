"""Cloud-only fixed-prefix vertex-ordering comparison; no exclusion evidence."""
import json
import os
from pathlib import Path
import re
from run_prototype import run, parse, sha

ROOT = Path(__file__).resolve().parent


def details(log):
    fields = parse(log)
    text = log.read_text()
    order = re.findall(r'^ORDER pick=(\d+) stop_reason=(\S+) maxleaf=(\d+)$', text, re.M)
    assert len(order) == 1
    pick, reason, maxleaf = order[0]
    fields.update(pick=int(pick), stop_reason=reason, maxleaf=int(maxleaf))
    fields['states'] = [list(map(int, row)) for row in re.findall(
        r'^STATE leaf=(\d+) key=(\d+) n1=(\d+)$', text, re.M)]
    assert fields['early_gate'] == 0
    return fields


def main():
    assert Path('/opt/e85/jobs').is_dir(), 'Existing cloud builder only'
    assert os.sched_getaffinity(0) == {0, 1}
    output = ROOT / 'prototype-heuristics'
    output.mkdir(exist_ok=False)
    source = ROOT / 'h3_phase2_heuristics.c'
    binary = output / 'profile'
    report = {'source_sha256': sha(source), 'runner_sha256': sha(Path(__file__)),
              'helper_sha256': sha(ROOT/'run_prototype.py'),
              'affinity': sorted(os.sched_getaffinity(0)),
              'child_address_space_bytes': 2*1024**3, 'child_cpu_seconds': 30,
              'child_wall_seconds': 30, 'scope': 'PROFILING_ONLY', 'runs': {}}
    report['compile'] = run(['gcc', '-O3', '-std=gnu11', str(source), '-o', str(binary)],
                            output/'compile.log')
    assert report['compile']['returncode'] == 0
    report['binary_sha256'] = sha(binary)
    common = [str(binary), '1', 'mrv=0', 'fc=0', 'pre=22', 'mod=384',
              'secs=20', 'nodes=2000000', 'earlygate=0', 'verbose=1']
    control = run(common+['res=-1', 'p1only=1', 'pick=0'], output/'control.log')
    assert control['returncode'] == 0 and not control['outer_timeout']
    control['profile'] = details(output/'control.log')
    expected = json.loads((ROOT/'profile-fixed-evidence/AUDIT.json').read_text())['profile']
    assert control['profile']['n1'] == expected['nodes']
    assert control['profile']['leaf1'] == expected['leaves']
    assert control['profile']['stopped'] == 0
    vectors = re.findall(r'^((?: \d+){384})$', (output/'control.log').read_text(), re.M)
    assert len(vectors) == 1 and list(map(int, vectors[0].split())) == expected['buckets']
    report['runs']['control'] = control
    for pick, label in enumerate(('baseline', 'slack', 'ratio', 'binomial')):
        result = run(common+['res=0', 'p1only=0', 'maxleaf=3', f'pick={pick}'],
                     output/(label+'.log'))
        if not result['outer_timeout']:
            result['profile'] = details(output/(label+'.log'))
            p = result['profile']
            assert p['pick'] == pick and p['maxleaf'] == 3
            assert result['returncode'] == (124 if p['stopped'] else 0)
            assert p['stop_reason'] in ('nodes', 'time', 'leaf-prefix', 'none')
            if p['stop_reason'] == 'leaf-prefix':
                assert p['leaf1'] == 4 and p['leafrun'] == 3
            if pick == 0:
                assert p['stop_reason'] == 'leaf-prefix'
                assert p['n2'] == 17+291381+1574657
            else:
                baseline = report['runs']['baseline']['profile']['states']
                assert p['states'] == baseline[:len(p['states'])]
        report['runs'][label] = result
    (output/'RUN.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2), flush=True)


if __name__ == '__main__':
    main()
