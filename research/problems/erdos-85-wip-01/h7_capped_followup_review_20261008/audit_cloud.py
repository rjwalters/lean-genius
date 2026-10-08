"""Read-only audit on the existing cloud builder; no solver or proof replay.

Run with python3 -B; emits a JSON bundle of the audit and base64 raw artifacts.
"""
import base64
import hashlib
import json
from pathlib import Path
import re
import subprocess

COMMIT = '4c8bab43fccd5b3f0250cf96d8ee2568f1818fdd'
JOB = '20261008T081402-commit-4c8bab43fccd-328154'
REPO = Path('/opt/e85/wt/commit-4c8bab43fccd')
R = 'research/problems/erdos-85-wip-01'
PKG = R + '/h7_hsb_campaign_20261008'
INPUTS = Path('/home/ec2-user/h7camp/inputs')
PINS = {'cadical': 'fd601b827c2f6e72c255dd27d6bfa9d7f982414181195fe3ea07ec81385772a2',
        'cake_lpr': '4d47ffdd19fc6a80e24025f8c5d27d89c4309c9931bdad6d389d87e35be5464b'}
EXPECTED = {('cube_F7_t0', 2061), ('cube_F7_t6', 119)}


def sha(data):
    return hashlib.sha256(data).hexdigest()


def main():
    assert subprocess.check_output(['git', '-C', str(REPO), 'rev-parse', 'HEAD']).decode().strip() == COMMIT
    files, hashes = {}, {}

    def retain(name, data):
        files[name] = base64.b64encode(data).decode()
        hashes[name] = sha(data)

    paths = [PKG + '/' + n for n in ['rerun_items.py', 'cert_item.py', 'h7_common.py', 'receipts/inputs.json']]
    paths.append(R + '/h1_cert_full_20261001/cert_row.py')
    for path in paths:
        data = (REPO / path).read_bytes()
        assert data == subprocess.check_output(['git', '-C', str(REPO), 'show', COMMIT + ':' + path]), path
        retain('sources/' + path.removeprefix(R + '/'), data)
    job = Path('/opt/e85/jobs') / JOB
    assert (job / 'exit').read_text().strip() == '0'
    for name in ['log', 'spec', 'exit']:
        retain('job.' + name, (job / name).read_bytes())
    log = (job / 'log').read_text()
    assert COMMIT in log and '--cap 7200 --heap-mb 4000' in log
    for cube, leaf in EXPECTED:
        assert f'{cube} {leaf} CERTIFIED ' in log
    raw = Path('/home/ec2-user/h7camp/sample/capped-followup.jsonl').read_bytes()
    retain('raw-followup.jsonl', raw)
    rows = [json.loads(line) for line in raw.splitlines()]
    assert len(rows) == 2 and {(r['cube'], r['leaf']) for r in rows} == EXPECTED
    meta_raw = (INPUTS / 'inputs.json').read_bytes()
    assert meta_raw == (REPO / PKG / 'receipts/inputs.json').read_bytes()
    assert sha(meta_raw) == 'f2d2be89aeee6603201649a70a64a6cdf4f20acc6e9268d502f686f0d39dcb6c'
    meta = json.loads(meta_raw)
    body = (INPUTS / 'canonical.body').read_bytes()
    assert sha(body) == meta['canonical_body_sha256']
    assert body.count(b'\n') == meta['canonical_clauses'] == 720804
    assert meta['variables'] == 17633 and meta['depth'] == 3
    for name, pin in PINS.items():
        assert sha((Path('/home/ec2-user/h7pilot/bin') / name).read_bytes()) == pin
    verified = []
    for row in rows:
        cube, leaf = row['cube'], row['leaf']
        m = meta['cubes'][cube]
        data = {ext: (INPUTS / f'{cube}.{ext}').read_bytes() for ext in ['units', 'hsb', 'cover']}
        for ext in data:
            assert sha(data[ext]) == m[ext + '_sha256'], (cube, ext)
        assert data['units'].count(b'\n') == 21
        assert data['hsb'].count(b'\n') == m['hsb_clauses']
        lines = data['cover'].splitlines()
        assert len(lines) == m['leaves']
        tokens = [int(x) for x in lines[leaf].split()]
        assert tokens[-1] == 0 and all(x < 0 for x in tokens[:-1])
        units = [-x for x in tokens[:-1]]
        assert len(units) == m['leaf_units'] and units == row['units']
        prefix = body + data['units'] + data['hsb']
        count = 720804 + 21 + m['hsb_clauses'] + len(units)
        cnf = f'p cnf 17633 {count}\n'.encode() + prefix + ''.join(f'{u} 0\n' for u in units).encode()
        assert sha(cnf) == row['cnf_sha256'] == row['expected_cnf_sha256']
        assert len(cnf) == row['cnf_bytes']
        assert row['schema'] == 'erdos85-h7-hsb-cert-v1'
        assert row['kind'] == 'leaf' and row['depth'] == 3
        assert row['status'] == 'CERTIFIED' and row['cap_seconds'] == 7200 and row['binaries'] == PINS
        s, c, p = row['solver'], row['checker'], row['proof']
        assert s['returncode'] == 20 and s['unsat_line'] is True
        assert c['returncode'] == 0 and c['verified_line'] is True and c['failure'] is None
        assert c['heap_mb'] == 4000
        assert p['bytes'] > 0 and p['checker_closed_early'] is False and p['stored'] is False
        assert p['format'] == 'cadical binary LRAT' and re.fullmatch('[0-9a-f]{64}', p['sha256'])
        verified.append({'cube': cube, 'leaf': leaf, 'cnf_sha256': sha(cnf),
                         'solver_cpu_seconds': s['cpu_seconds'], 'checker_cpu_seconds': c['cpu_seconds'],
                         'proof_bytes': p['bytes'], 'proof_sha256': p['sha256']})
    audit = {'status': 'CAPPED_FOLLOWUP_RECEIPT_AUDIT_PASS', 'producer_commit': COMMIT,
             'producer_job': JOB, 'authoritative_exit': 0, 'verified': verified,
             'artifact_sha256': hashes,
             'scope': 'Source pins, current approved binary bytes, reconstructed CNF identities, and producer receipts. Proof streams were discarded; no independent proof replay or fresh Lean emitter check. Original censored cost sample unchanged.'}
    print(json.dumps({'audit': audit, 'files': files}))


if __name__ == '__main__':
    main()
