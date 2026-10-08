"""Independent cloud-only receipt, input and estimate audit; no solver or Lean.

Reconstructs CNF hashes directly from the frozen bytes, without importing the
campaign generator or estimator. A passing result validates the recorded sample,
not all leaves or the truth of unrecorded checker runs.
"""
from collections import Counter
from datetime import datetime
import hashlib
import json
import math
from pathlib import Path
import platform
import random
import re

ROOT = Path(__file__).resolve().parent
INPUTS = Path('/home/ec2-user/h7camp/inputs')
SAMPLE = Path('/home/ec2-user/h7camp/sample/results.jsonl')
JOB = Path('/opt/e85/jobs/20261008T050835-commit-50a06c7c033a-210080')
INPUT_SHA = 'f2d2be89aeee6603201649a70a64a6cdf4f20acc6e9268d502f686f0d39dcb6c'
SAMPLE_SHA = '8a244515666117ce4d4592c396a5bfa434e2affc8f4b0bb677e31c5a1bac8477'
RAW_SHA = 'b93066071de9969416f0d3267082b1a97ca52fc97d5a173b26afe228716ce97d'
BINS = {'cadical': 'fd601b827c2f6e72c255dd27d6bfa9d7f982414181195fe3ea07ec81385772a2',
        'cake_lpr': '4d47ffdd19fc6a80e24025f8c5d27d89c4309c9931bdad6d389d87e35be5464b'}
PAIRS = [(6, 5), (6, 8), (6, 14), (6, 15), (6, 16), (6, 17), (6, 18),
         (7, 0), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 8), (7, 9),
         (7, 10), (7, 11), (7, 13), (7, 14),
         (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (9, 0), (9, 1)]


def require(value, message):
    if not value:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def read(path):
    def unique(items):
        result = {}
        for key, value in items:
            require(key not in result, 'Duplicate JSON key: ' + key)
            result[key] = value
        return result
    return json.loads(path.read_text(), object_pairs_hook=unique)


def record_key(record):
    return record['cube'], record['kind'], record['leaf']


def check_result(record, expected_hash, expected_bytes, units):
    require(record['schema'] == 'erdos85-h7-hsb-cert-v1' and record['depth'] == 3 and
            record['cap_seconds'] == 3600 and record['seed'] == 20261008 and
            record['binaries'] == BINS, 'Wrong receipt scope or binary pins')
    require(record['cnf_sha256'] == record['expected_cnf_sha256'] == expected_hash and
            record['cnf_bytes'] == expected_bytes, 'CNF identity mismatch')
    if units is not None:
        require(record['units'] == units, 'Wrong positive leaf units')
    solver, checker, proof = record['solver'], record['checker'], record['proof']
    require(checker['heap_mb'] == 2000 and checker['failure'] is None and
            'heap_retry_of' not in record, 'Unexpected heap change or checker failure')
    require(proof['format'] == 'cadical binary LRAT' and proof['stored'] is False and
            proof['checker_closed_early'] is False and type(proof['bytes']) is int and proof['bytes'] > 0 and
            re.fullmatch('[0-9a-f]{64}', proof['sha256']) is not None, 'Invalid streamed proof receipt')
    for process in (solver, checker):
        for field in ('cpu_seconds', 'wall_seconds', 'maxrss'):
            value = process[field]
            require(type(value) in (int, float) and math.isfinite(value) and value >= 0,
                    'Invalid process metric')
    require(datetime.fromisoformat(record['started_utc'].replace('Z', '+00:00')) <=
            datetime.fromisoformat(record['finished_utc'].replace('Z', '+00:00')), 'Reversed timestamps')
    if record['status'] == 'CERTIFIED':
        require(solver['returncode'] == 20 and solver['unsat_line'] is True and
                checker['returncode'] == 0 and checker['verified_line'] is True,
                'Certified status without solver/checker evidence')
    else:
        require(record['status'] == 'SOLVER_TIMEOUT' and solver['returncode'] == 0 and
                solver['unsat_line'] is False and checker['verified_line'] is False and
                3599 <= solver['wall_seconds'] <= 3610, 'Unexplained non-certified result')


def main():
    require(platform.system() == 'Linux' and INPUTS.is_dir() and JOB.is_dir(), 'Cloud builder only')
    source = read(ROOT / 'SOURCE.json')
    for name, expected in source['files_sha256'].items():
        require(sha((ROOT / 'reviewed' / name).read_bytes()) == expected, 'Reviewed file changed: ' + name)
    input_bytes = (INPUTS / 'inputs.json').read_bytes()
    require(sha(input_bytes) == INPUT_SHA and input_bytes ==
            (ROOT / 'reviewed/receipts/inputs.json').read_bytes(), 'Frozen inputs differ')
    meta = json.loads(input_bytes)
    require(meta['depth'] == 3 and meta['variables'] == 17633 and meta['canonical_clauses'] == 720804,
            'Wrong formula parameters')
    require(set(meta['cubes']) == {f'cube_F{f}_t{i}' for f, i in PAIRS} and
            meta['total_leaves'] == sum(c['leaves'] for c in meta['cubes'].values()) == 377776,
            'Wrong cube or leaf inventory')
    sample_bytes = (ROOT / 'reviewed/receipts/sample_results.jsonl').read_bytes()
    raw_bytes = SAMPLE.read_bytes()
    require(sha(sample_bytes) == SAMPLE_SHA and sha(raw_bytes) == RAW_SHA, 'Sample bytes changed')
    rows = [json.loads(line) for line in sample_bytes.splitlines() if line.strip()]
    raw_rows = [json.loads(line) for line in raw_bytes.splitlines() if line.strip()]
    require(len(rows) == len(raw_rows) == 1428, 'Wrong sample size')
    raw_by_key = {record_key(r): r for r in raw_rows}
    require(len(raw_by_key) == len({record_key(r) for r in rows}) == 1428, 'Duplicate sample item')
    for row in rows:
        require(row.get('sampler') == 'main' and
                {k: v for k, v in row.items() if k != 'sampler'} == raw_by_key[record_key(row)],
                'Committed sample differs from primary raw receipt')
    require((JOB / 'exit').read_text().strip() == '0' and
            '[e85] commit 50a06c7c033ac8b63a7f9695e7dc7cfd15b38a28 ' in (JOB / 'log').read_text(),
            'Missing primary job provenance or terminal exit')
    for name, expected in BINS.items():
        require(sha((Path('/home/ec2-user/h7pilot/bin') / name).read_bytes()) == expected,
                'Current approved binary differs: ' + name)
    body = (INPUTS / 'canonical.body').read_bytes()
    require(sha(body) == meta['canonical_body_sha256'] and body.count(b'\n') == 720804,
            'Canonical body differs')
    make_header = lambda count: f'p cnf 17633 {count}\n'.encode()
    estimate = read(ROOT / 'reviewed/receipts/estimate.json')
    cube_estimates = {row['cube']: row for row in estimate['cubes']}
    total_cpu = expected_capped = capped_cpu = proof_bytes = 0.0
    bootstrap = [0.0] * 5000
    rng = random.Random(1)
    checked = []
    for name, info in meta['cubes'].items():
        cube_rows = [row for row in rows if row['cube'] == name]
        covers = [row for row in cube_rows if row['kind'] == 'cover']
        leaves = [row for row in cube_rows if row['kind'] == 'leaf']
        require(len(cube_rows) == 51 and len(covers) == 1 and len(leaves) == 50, 'Unbalanced sample')
        selected = random.Random(f'20261008:{name}').sample(range(info['leaves']), 50)
        require({row['leaf'] for row in leaves} == set(selected) and
                all(row['sample_index'] == selected.index(row['leaf']) for row in leaves),
                'Sample differs from frozen random selection')
        units, hsb, cover = [(INPUTS / (name + '.' + ext)).read_bytes() for ext in ('units', 'hsb', 'cover')]
        for ext, data in (('units', units), ('hsb', hsb), ('cover', cover)):
            require(sha(data) == info[ext + '_sha256'], 'Changed cube input: ' + name + '.' + ext)
        cover_lines = cover.splitlines()
        require(units.count(b'\n') == 21 and hsb.count(b'\n') == info['hsb_clauses'] and
                len(cover_lines) == info['leaves'], 'Input clause counts differ')
        cube_body = body + units
        require(sha(make_header(720825) + cube_body) == info['cube_cnf_sha256'], 'Cube hash differs')
        all_body = cube_body + hsb
        clauses = 720825 + info['hsb_clauses']
        require(sha(make_header(clauses) + all_body) == info['hsb_cnf_sha256'], 'HSB hash differs')
        cover_cnf = make_header(clauses + info['leaves']) + all_body + cover
        require(sha(cover_cnf) == info['cover_cnf_sha256'], 'Cover hash differs')
        check_result(covers[0], sha(cover_cnf), len(cover_cnf), None)
        require(covers[0]['status'] == 'CERTIFIED' and covers[0]['leaf'] is None and
                covers[0]['sample_index'] is None, 'Uncertified or misidentified cover')
        prefix = make_header(clauses + info['leaf_units']) + all_body
        prefix_hash = hashlib.sha256(prefix)
        for row in leaves:
            literals = [int(token) for token in cover_lines[row['leaf']].split()]
            require(literals[-1] == 0 and len(literals) - 1 == info['leaf_units'] and
                    all(-17633 <= value < 0 for value in literals[:-1]), 'Bad blocking clause')
            positive = [-value for value in literals[:-1]]
            tail = ''.join(f'{value} 0\n' for value in positive).encode()
            h = prefix_hash.copy()
            h.update(tail)
            check_result(row, h.hexdigest(), len(prefix) + len(tail), positive)
        values = [row['solver']['cpu_seconds'] + row['checker']['cpu_seconds'] for row in leaves]
        counted = sum(values) * info['leaves'] / 50 / 3600
        require(math.isclose(counted, cube_estimates[name]['cpu_h'], rel_tol=1e-12), 'Per-cube cost differs')
        total_cpu += counted
        capped = [row for row in leaves if row['status'] == 'SOLVER_TIMEOUT']
        expected_capped += len(capped) * info['leaves'] / 50
        capped_cpu += sum(row['solver']['cpu_seconds'] + row['checker']['cpu_seconds'] for row in capped) * info['leaves'] / 50 / 3600
        proof_bytes += sum(row['proof']['bytes'] for row in leaves) * info['leaves'] / 50
        for index in range(5000):
            bootstrap[index] += sum(values[rng.randrange(50)] for _ in range(50)) / 50 * info['leaves'] / 3600
        checked.append({'cube': name, 'sampled': 50, 'certified': 50 - len(capped),
                        'capped': len(capped), 'leaves': info['leaves'], 'cpu_hours': counted})
    statuses = dict(Counter(row['kind'] + ':' + row['status'] for row in rows))
    require(statuses == {'cover:CERTIFIED': 28, 'leaf:CERTIFIED': 1398, 'leaf:SOLVER_TIMEOUT': 2},
            'Unexpected outcome inventory')
    bootstrap.sort()
    interval = [round(bootstrap[250]), round(bootstrap[4750])]
    require(round(total_cpu) == estimate['cpu_hours'] == 3856 and
            interval == estimate['cpu_hours_5_95'] == [2864, 5216] and
            round(expected_capped) == estimate['expected_capped_leaves'] == 720 and
            round(capped_cpu) == estimate['cpu_hours_counted_for_capped_leaves'] == 766 and
            round(proof_bytes / 1e12, 1) == estimate['proof_tb_streamed'] == 20.1,
            'Estimate summary differs')
    require(estimate['utilisation_assumed'] == 0.85 and
            round(total_cpu / 0.85 * 0.0147) == estimate['usd_spot'][1] == 67,
            'Conditional dollar arithmetic differs')
    require(SAMPLE.read_bytes() == raw_bytes and (INPUTS / 'inputs.json').read_bytes() == input_bytes,
            'Evidence changed during audit')
    print(json.dumps({'status': 'COST_SAMPLE_RECEIPT_AND_ARITHMETIC_AUDIT_PASS',
        'review_commit': source['commit'], 'auditor_sha256': sha(Path(__file__).read_bytes()),
        'inputs_sha256': INPUT_SHA, 'sample_sha256': SAMPLE_SHA, 'raw_sample_sha256': RAW_SHA,
        'primary_job': JOB.name, 'primary_job_exit': 0, 'primary_job_log_sha256': sha((JOB / 'log').read_bytes()),
        'status_counts': statuses, 'sample_seed': 20261008, 'sampled_leaves': 1400,
        'total_campaign_leaves': 377776, 'cpu_hours': total_cpu, 'bootstrap_5_95_rounded': interval,
        'expected_capped_leaves': expected_capped, 'cpu_hours_counted_for_capped_leaves': capped_cpu,
        'proof_tb_streamed': proof_bytes / 1e12, 'conditional_cost_usd': total_cpu / 0.85 * 0.0147,
        'timeouts': [{'cube': row['cube'], 'leaf': row['leaf']} for row in rows if row['status'] != 'CERTIFIED'],
        'cubes': checked, 'full_campaign_complete': False,
        'scope': 'Recorded sample receipt identities and internally consistent solver/checker outcomes; '
                 'independently reconstructed CNF hashes, deterministic sample selection, primary receipt equality, '
                 'and estimate arithmetic. Proof streams were discarded and were not rechecked. '
                 'The interval describes a censored empirical bootstrap, not a completion-time bound. '
                 'The dollar result uses stated price/utilisation assumptions, not current billing verification.'}, indent=2))


if __name__ == '__main__':
    main()
