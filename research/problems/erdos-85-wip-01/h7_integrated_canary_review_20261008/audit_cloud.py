"""Read-only cloud receipt audit of the integrated canary local-store E2E run.

Prints a JSON bundle with raw evidence; does not run solvers or claim AWS readiness.
"""
import argparse
import base64
import hashlib
import json
from pathlib import Path
import subprocess

COMMIT = '797579e113ab59e1bcbcb93eb0b84540b628ded0'
JOB = '20261008T085923-commit-797579e113ab-359334'
R = 'research/problems/erdos-85-wip-01'
PKG = R + '/h7_hsb_campaign_20261008'
PINS = {'cadical': 'fd601b827c2f6e72c255dd27d6bfa9d7f982414181195fe3ea07ec81385772a2',
        'cake_lpr': '4d47ffdd19fc6a80e24025f8c5d27d89c4309c9931bdad6d389d87e35be5464b'}


def sha(data):
    return hashlib.sha256(data).hexdigest()


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--repository', type=Path, required=True)
    a = p.parse_args()
    repo = a.repository.resolve()
    assert str(repo).startswith('/opt/e85/wt/'), 'Existing cloud builder only'
    assert subprocess.check_output(['git', '-C', str(repo), 'rev-parse', 'HEAD']).decode().strip() == COMMIT
    files, hashes = {}, {}

    def retain(name, data):
        files[name] = base64.b64encode(data).decode()
        hashes[name] = sha(data)

    names = ['cert_worker.py', 'cert_controller.py', 'cert_bootstrap.sh', 'h7_common.py',
             'cert_item.py', 'cert_batch.py', 'collect_receipts.py', 'test_campaign.py',
             'e2e_test.sh', 'README.md', 'receipts/inputs.json']
    for name in names:
        path = PKG + '/' + name
        data = (repo / path).read_bytes()
        assert data == subprocess.check_output(['git', '-C', str(repo), 'show', COMMIT + ':' + path]), name
        retain('sources/' + name, data)
    for name in ['h1_cert_full_20261001/cert_row.py', 'phase_b_h1_verdict_cloud_20260921/controller.py']:
        path = R + '/' + name
        data = (repo / path).read_bytes()
        assert data == subprocess.check_output(['git', '-C', str(repo), 'show', COMMIT + ':' + path]), name
        retain('dependencies/' + name, data)
    job = Path('/opt/e85/jobs') / JOB
    assert (job / 'exit').read_text().strip() == '0'
    for name in ['log', 'spec', 'exit']:
        retain('job.' + name, (job / name).read_bytes())
    log = (job / 'log').read_text()
    assert COMMIT in log and 'Ran 16 tests' in log and '\nOK\n' in log and 'E2E_ALL_PASS' in log
    e2e = Path('/home/ec2-user/h7camp/e2e')
    raw = e2e.with_suffix('.log').read_bytes()
    retain('e2e.log', raw)
    lines = raw.decode().splitlines()
    assert sum(line.startswith('PASS ') for line in lines) == 12
    assert not any(line.startswith('FAIL ') for line in lines) and lines[-1] == 'E2E_ALL_PASS'
    inputs = Path('/home/ec2-user/h7camp/inputs/inputs.json').read_bytes()
    assert inputs == (repo / PKG / 'receipts/inputs.json').read_bytes()
    manifest = (e2e / 'manifest.jsonl').read_bytes()
    retain('manifest.jsonl', manifest)
    rows = [json.loads(line) for line in manifest.splitlines()]
    expected = set()
    for row in rows:
        if row['kind'] == 'cover':
            expected.add((row['cube'], 'cover', None))
        else:
            leaves = row['leaves'] if 'leaves' in row else range(row['start'], row['end'])
            expected.update((row['cube'], 'leaf', leaf) for leaf in leaves)
    assert len(rows) == 5 and len(expected) == 21
    ledgers = []
    for path in sorted((e2e / 'store/ledger').glob('*.json')):
        ledger = json.loads(path.read_text())
        assert ledger['status'] == 'CERTIFIED' and ledger['certified'] == ledger['items']
        assert ledger['checkout_head'] == COMMIT
        assert ledger['inputs_json_sha256'] == sha(inputs) and ledger['manifest_sha256'] == sha(manifest)
        ledgers.append(ledger)
    assert len(ledgers) == 5 and {l['id'] for l in ledgers} == {r['id'] for r in rows}
    recovered, = [l for l in ledgers if l['id'] == 'cube_F9_t1-x0']
    assert recovered['carried'] == 3 and recovered['node'] == 'i-test-b'
    found = set()
    for path in sorted((e2e / 'store/results').glob('*.jsonl.zst')):
        data = subprocess.check_output(['zstd', '-dc', str(path)])
        for line in data.splitlines():
            item = json.loads(line)
            key = (item['cube'], item['kind'], item.get('leaf'))
            assert key in expected and key not in found, key
            found.add(key)
            assert item['status'] == 'CERTIFIED' and item['binaries'] == PINS
            assert item['solver']['returncode'] == 20 and item['checker']['verified_line'] is True
            assert not item['proof']['checker_closed_early'] and item['proof']['bytes'] > 0
            assert len(item['proof']['sha256']) == 64
    assert found == expected
    assert (e2e / 'store-alarm/control/STOP').is_file()
    assert list((e2e / 'store-alarm/control').glob('ALARM-*'))
    assert len(list((e2e / 'store-alarm/claims').iterdir())) == 1
    alarm_ledgers = [json.loads(f.read_text()) for f in (e2e / 'store-alarm/ledger').glob('*.json')]
    assert alarm_ledgers and all(l['status'] != 'CERTIFIED' for l in alarm_ledgers)
    assert not (e2e / 'store-unpinned/claims').exists() and not (e2e / 'store-mem/claims').exists()
    cap, = [json.loads(f.read_text()) for f in (e2e / 'store-cap/ledger').glob('*.json')]
    assert cap['status'] == 'INCOMPLETE' and not (e2e / 'store-cap/control/STOP').exists()
    assert any(i['status'] == 'SOLVER_TIMEOUT' for i in cap['not_certified'])
    for path in sorted(e2e.rglob('*')):
        if path.is_file() and path.suffix in {'.json', '.jsonl', '.zst', '.log'}:
            retain('e2e/' + str(path.relative_to(e2e)), path.read_bytes())
    result = {'status': 'INTEGRATED_LOCAL_STORE_E2E_AUDIT_PASS', 'commit': COMMIT, 'job': JOB,
              'authoritative_exit': 0, 'unit_tests_reported': 16, 'e2e_checks': 12,
              'certified_unique_items': len(found), 'certified_ledgers': len(ledgers), 'carried_items': 3,
              'artifact_sha256': hashes,
              'scope': 'Source identity and actual retained E2E receipts; no proof replay, fresh CNF reconstruction, AWS path test, full canary or campaign credit.'}
    print(json.dumps({'audit': result, 'files': files}))


if __name__ == '__main__':
    main()
