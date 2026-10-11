"""Bounded C ratio-order bucket-zero sizing; phase three is omitted."""
import json
import os
from pathlib import Path
import re
from run_prototype import run, sha
from run_heuristics import details

ROOT = Path(__file__).resolve().parent


def main():
    assert Path('/opt/e85/jobs').is_dir()
    assert os.sched_getaffinity(0) == {0, 1}
    output = ROOT/'prototype-bucket-zero'
    output.mkdir(exist_ok=False)
    source = ROOT/'h3_phase2_heuristics.c'
    binary = output/'profile'
    names = ['h3_phase2_heuristics.c', 'run_bucket_zero.py',
             'run_prototype.py', 'run_heuristics.py']
    report = {'source_hashes': {n: sha(ROOT/n) for n in names}, 'scope': 'PROFILING_ONLY',
              'affinity': sorted(os.sched_getaffinity(0)), 'child_address_space_bytes': 2*1024**3,
              'child_cpu_seconds': 30, 'child_wall_seconds': 30, 'runs': {}}
    report['compile'] = run(['gcc', '-O3', '-std=gnu11', str(source), '-o', str(binary)],
                            output/'compile.log')
    assert report['compile']['returncode'] == 0
    report['binary_sha256'] = sha(binary)
    common = [str(binary), '1', 'mrv=0', 'fc=0', 'pre=22', 'mod=384',
              'secs=20', 'nodes=2000000', 'earlygate=0', 'verbose=1', 'pick=2']
    for label, args in [('control', ['res=-1', 'p1only=1']),
                        ('bucket-zero', ['res=0', 'p1only=0', 'maxleaf=0'])]:
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
                if not p['stopped']:
                    assert p['leaf1'] == p['leafrun'] == 4 and p['n1'] == 8167
        report['runs'][label] = result
    (output/'RUN.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2), flush=True)


if __name__ == '__main__':
    main()
