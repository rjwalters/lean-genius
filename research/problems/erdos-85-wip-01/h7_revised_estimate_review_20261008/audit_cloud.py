"""Recompute H7 estimates on existing builder from a JSON stdin snapshot.

No solver or Lean. Four fixed-seed bootstrap runs compare archive/raw order.
"""
import hashlib
import json
import math
from pathlib import Path
import platform
import random
import sys


def sha(b):
    return hashlib.sha256(b).hexdigest()


def key(r):
    return r['cube'], r['kind'], r.get('leaf')


def calculate(meta, rows):
    rng = random.Random(1)
    boots = [0.0] * 5000
    total = proof = 0.0
    for cube, info in meta['cubes'].items():
        rs = [r for r in rows if r['cube'] == cube and r['kind'] == 'leaf']
        assert len(rs) == 50
        xs = [r['solver']['cpu_seconds'] + r['checker']['cpu_seconds'] for r in rs]
        total += math.fsum(xs) * info['leaves'] / 50 / 3600
        proof += sum(r['proof']['bytes'] for r in rs) * info['leaves'] / 50
        for i in range(5000):
            boots[i] += sum(xs[rng.randrange(50)] for _ in range(50)) / 50 * info['leaves'] / 3600
    boots.sort()
    return {'cpu_hours': total, 'cpu_hours_rounded': round(total),
            'bootstrap_5_95': [round(boots[250]), round(boots[4750])],
            'bootstrap_5_95_unrounded': [boots[250], boots[4750]],
            'proof_tb': proof / 1e12}


def main():
    assert platform.system() == 'Linux' and Path('/opt/e85/jobs').is_dir()
    bundle = json.load(sys.stdin)
    files = bundle['files']
    for name, value in files.items():
        assert sha(value.encode()) == bundle['sha256'][name], name
    meta = json.loads(files['inputs.json'])
    old = [json.loads(x) for x in files['old-sample.jsonl'].splitlines()]
    new = [json.loads(x) for x in files['new-sample.jsonl'].splitlines()]
    followup = [json.loads(x) for x in files['followup.jsonl'].splitlines()]
    assert len(old) == len(new) == len({key(r) for r in new}) == 1428
    assert [key(r) for r in old] == [key(r) for r in new]
    old_by, follow_by = {key(r): r for r in old}, {key(r): r for r in followup}
    assert set(follow_by) == {('cube_F7_t0', 'leaf', 2061), ('cube_F7_t6', 'leaf', 119)}
    for row in new:
        original = old_by[key(row)]
        expected = original
        if key(row) in follow_by:
            assert original['status'] == 'SOLVER_TIMEOUT'
            expected = dict(follow_by[key(row)], seed=original['seed'], sample_index=original['sample_index'],
                            replaces_capped_sample={'cap_seconds': original['cap_seconds'],
                            'conflicts': original['solver']['conflicts'],
                            'solver_cpu_seconds': original['solver']['cpu_seconds']})
        assert row == expected, key(row)
        assert row['status'] == 'CERTIFIED'
    raw_bytes = Path('/home/ec2-user/h7camp/sample/results.jsonl').read_bytes()
    assert sha(raw_bytes) == 'b93066071de9969416f0d3267082b1a97ca52fc97d5a173b26afe228716ce97d'
    raw = [json.loads(x) for x in raw_bytes.splitlines()]
    assert {key(r) for r in raw} == set(old_by)
    raw_followup = [follow_by.get(key(r), r) for r in raw]
    results = {name: calculate(meta, rs) for name, rs in [
        ('old_archive_order', old), ('old_raw_order', raw),
        ('new_archive_order', new), ('new_raw_order', raw_followup)]}
    published = {name: json.loads(files[name + '-estimate.json']) for name in ('old', 'new')}
    for name in ('old', 'new'):
        for order in ('archive', 'raw'):
            r = results[name + '_' + order + '_order']
            r['matches_published_point'] = r['cpu_hours_rounded'] == published[name]['cpu_hours']
            r['matches_published_bootstrap'] = r['bootstrap_5_95'] == published[name]['cpu_hours_5_95']
    print(json.dumps({'status': 'ESTIMATE_RECOMPUTATION', 'commit': bundle['commit'],
                      'source_sha256': bundle['sha256'], 'python': sys.version,
                      'bootstrap_replicates': 5000, 'random_seed': 1,
                      'sample_substitution_identity': 'PASS',
                      'published_intervals': {k: v['cpu_hours_5_95'] for k, v in published.items()},
                      'results': results}, indent=2))


if __name__ == '__main__':
    main()
