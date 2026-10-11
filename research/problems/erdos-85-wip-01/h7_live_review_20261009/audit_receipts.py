"""Audit captured canary v2 metadata, without invoking Lean, SAT, or cloud writes.

Independent formula-byte reconstruction is a separate cloud step; absent that
expected-input ledger this deliberately does not issue full canary acceptance.
"""
import argparse
import base64
import hashlib
import json
import math
import re
import subprocess
from pathlib import Path

PIN = '729127aa817263475e7aa0c65c3db34a65da3389'
INPUT = 'f2d2be89aeee6603201649a70a64a6cdf4f20acc6e9268d502f686f0d39dcb6c'
MANIFEST = '0deb438f9bd7f5cfb840fd799330e6b80e70a043b21f96fcf0737c826515290c'
PREFIX = 'sat49/h7hsb-20261008-canary'
BINS = {'cadical': 'fd601b827c2f6e72c255dd27d6bfa9d7f982414181195fe3ea07ec81385772a2',
        'cake_lpr': '4d47ffdd19fc6a80e24025f8c5d27d89c4309c9931bdad6d389d87e35be5464b'}
COVERS = ['cube_F6_t14', 'cube_F7_t10']
TAILS = ['cube_F6_t16', 'cube_F6_t18', 'cube_F7_t10', 'cube_F7_t13', 'cube_F8_t0', 'cube_F9_t0']
ROWS = {c+'-cover': (c, [None]) for c in COVERS}
ROWS.update({'cube_F6_t14-h0000': ('cube_F6_t14', list(range(4))),
             'cube_F6_t14-h0001': ('cube_F6_t14', list(range(4, 8)))})
ROWS.update({c+'-b0000': (c, list(range(1024, 1088))) for c in TAILS})


def sha(data):
    return hashlib.sha256(data).hexdigest()


def read(path):
    return json.loads(path.read_bytes())


def normalized(receipt):
    return {k: v for k, v in receipt.items() if k != 'carried'}


def item_check(r, bid, cube, leaf, hosts, meta):
    assert r['schema'] == 'erdos85-h7-hsb-cert-v1'
    assert (r['batch'], r['cube'], r['leaf'], r['kind']) == (bid, cube, leaf, 'cover' if leaf is None else 'leaf')
    assert r['status'] == 'CERTIFIED' and r['depth'] == 3
    assert r['binaries'] == BINS and r['cap_seconds'] == 7200
    assert r['host'] in hosts and r['started_utc'] <= r['finished_utc']
    assert re.fullmatch('[0-9a-f]{64}', r['cnf_sha256'])
    assert r['cnf_sha256'] == r['expected_cnf_sha256'] and r['cnf_bytes'] > 0
    assert r['solver']['returncode'] == 20 and r['solver']['unsat_line'] is True
    assert r['checker']['returncode'] == 0 and r['checker']['verified_line'] is True
    assert r['checker']['heap_mb'] == 6000 and r['checker'].get('failure') is None
    for part in ('solver', 'checker'):
        for field in ('cpu_seconds', 'wall_seconds'):
            assert math.isfinite(r[part][field]) and r[part][field] >= 0
    proof = r['proof']
    assert proof['bytes'] > 0 and re.fullmatch('[0-9a-f]{64}', proof['sha256'])
    assert proof['checker_closed_early'] is False and proof['stored'] is (leaf is None)
    assert proof['format'] == 'cadical binary LRAT'
    if leaf is None:
        assert r['cnf_sha256'] == meta['cubes'][cube]['cover_cnf_sha256']
    else:
        assert len(r['units']) == meta['cubes'][cube]['leaf_units']
        assert len(set(r['units'])) == len(r['units'])
        assert all(type(x) is int and 1 <= x <= 17633 for x in r['units'])
        assert r['solver']['maxrss'] > 0 and r['checker']['maxrss'] > 0


def audit(root, inputs, expected=None):
    snapshot = root/'snapshot1'
    for folder in (snapshot, root/'supplement1'):
        for name, digest in read(folder/'CAPTURE.json')['retained_sha256'].items():
            assert sha((folder/name).read_bytes()) == digest, name
    raw = inputs.read_bytes()
    assert sha(raw) == INPUT
    meta = json.loads(raw)
    objects = {r['Key']: r for r in read(snapshot/'canary-objects.json')['Contents']}
    controls = {k.removeprefix(PREFIX+'/control/') for k in objects if k.startswith(PREFIX+'/control/')}
    assert controls == {'STOP', 'STOP-CAUSE'}, controls
    cause = read(snapshot/'canary/control/STOP-CAUSE')
    assert cause['action'] == 'all batches CERTIFIED; stopping'
    hosts = {}
    nodes = {}
    for node in (snapshot/'canary/nodes').iterdir():
        bootstrap = (node/'bootstrap.log').read_text()
        assert 'bootstrap ok' in bootstrap and 'BOOTSTRAP-FAIL' not in bootstrap
        assert 'head='+PIN in bootstrap and 'inputs='+INPUT in bootstrap and 'manifest='+MANIFEST in bootstrap
        tools = (node/'tools.build.txt').read_text()
        for binary, digest in BINS.items():
            assert digest+'  /usr/local/bin/'+binary in tools
        host = re.search(r'^Linux (\S+)', tools, re.M).group(1)
        hosts[host] = node.name
        status = read(node/'status.json')
        assert status['errors'] == 0 and not (node/'e85-h7hsb.err').read_text().strip()
        mem_budget = 363 if status['instance_type'] == 'r8g.12xlarge' else 486
        assert status['slots'] * 7.5 <= mem_budget
        nodes[node.name] = {'host': host, 'slots': status['slots'], 'instance_type': status['instance_type']}
    all_receipts = []
    seen = set()
    summaries = []
    for path in sorted((snapshot/'canary/ledger').glob('*.json')):
        l = read(path)
        bid = l['id']
        assert bid in ROWS and bid not in seen
        seen.add(bid)
        cube, leaves = ROWS[bid]
        assert (l['cube'], l['kind']) == (cube, 'cover' if leaves == [None] else 'leaves')
        assert l['checkout_head'] == PIN and l['inputs_json_sha256'] == INPUT and l['manifest_sha256'] == MANIFEST
        assert l['node'] in nodes and l['instance_type'] == nodes[l['node']]['instance_type']
        assert 0 <= l['slot'] < nodes[l['node']]['slots']
        assert l['status'] == 'CERTIFIED' and l['batch_returncode'] == 0 and l['not_certified'] == []
        assert l['items'] == l['ran'] == l['certified'] == len(leaves)
        assert l['statuses'] == {'CERTIFIED': len(leaves)}
        assert l['results_key'] == PREFIX+'/results/'+path.name.removesuffix('.json')+'.jsonl.zst'
        packed = snapshot/'canary/results'/Path(l['results_key']).name
        assert sha(packed.read_bytes()) == l['results_sha256']
        data = subprocess.check_output(['zstd', '-dc', str(packed)])
        assert sha(data) == l['receipts_sha256']
        receipts = [json.loads(line) for line in data.splitlines()]
        assert [r['leaf'] for r in receipts] == leaves
        partials = []
        for p in (snapshot/'canary/partial').glob(bid+'.*.jsonl'):
            partials.extend(json.loads(line) for line in p.read_bytes().splitlines())
        for r in receipts:
            item_check(r, bid, cube, r['leaf'], hosts, meta)
            if r.get('carried'):
                assert any(normalized(r) == normalized(pr) for pr in partials), (bid, r['leaf'], 'missing carry provenance')
            else:
                assert hosts[r['host']] == l['node']
        assert l['carried'] == sum(bool(r.get('carried')) for r in receipts)
        assert l['proof_bytes'] == sum(r['proof']['bytes'] for r in receipts)
        for part in ('solver', 'checker'):
            assert math.isclose(l[part+'_cpu_seconds'], sum(r[part]['cpu_seconds'] for r in receipts), rel_tol=1e-12)
        if leaves == [None]:
            r = receipts[0]
            retained = read(root/'supplement1'/(cube+'.cover.json'))
            assert l['retained'] == [cube+'.cover.'+ext for ext in ('cnf', 'lrat', 'json')]
            assert retained['binaries'] == BINS and retained['solver'] == r['solver']
            assert retained['cube'] == cube and retained['depth'] == 3 and retained['variables'] == 17633
            assert retained['extension']['order'] == ['cube', 'hsb', 'cover']
            for field in ('bytes', 'sha256'):
                assert retained['cnf'][field] == r['cnf_'+field]
                assert retained['proof'][field] == r['proof'][field]
            for ext, size in [('cnf', r['cnf_bytes']), ('lrat', r['proof']['bytes'])]:
                assert objects[PREFIX+'/covers-retained/'+cube+'.cover.'+ext]['Size'] == size
        else:
            assert l['retained'] == []
        summaries.append({'batch': bid, 'items': len(receipts), 'carried': l['carried'], 'node': l['node']})
        all_receipts.extend(receipts)
    assert seen == set(ROWS) and len(all_receipts) == 394
    assert len(list((snapshot/'canary/results').glob('*'))) == 10
    fleets = {f['FleetId']: f for f in read(snapshot/'fleets.json')['Fleets']}
    assert fleets['fleet-d57fe55e-20a4-4cb1-ba3e-3562f2608b82']['FleetState'] == 'deleted'
    instances = {i['InstanceId']: i for r in read(snapshot/'instances.json')['Reservations'] for i in r['Instances']}
    for iid in ('i-0da45fb9523dc10e3', 'i-06d91affb3e08f4e0'):
        assert instances[iid]['State']['Name'] == 'terminated'
    for i in instances.values():
        tags = {t['Key']: t['Value'] for t in i.get('Tags', [])}
        if tags.get('project') == 'e85-h7hsb-20261008-canary':
            assert i['State']['Name'] == 'terminated'
    for role in ('main', 'canary'):
        userdata = base64.b64decode(read(snapshot/(role+'-template.json'))['LaunchTemplateVersions'][0]['LaunchTemplateData']['UserData']).decode()
        for token in ('git checkout --detach '+PIN[:11], INPUT, MANIFEST, "E85_HEAP_MB='6000'", "E85_CAP='7200'"):
            assert token in userdata
    independent = False
    if expected:
        ex = read(expected)
        assert ex['inputs_sha256'] == INPUT and ex['heap_mb'] == 6000 and set(ex['batches']) == set(ROWS)
        indexed = {(bid, r['leaf']): r for bid, rows in ex['batches'].items() for r in rows}
        assert len(indexed) == 394
        for r in all_receipts:
            e = indexed[r['batch'], r['leaf']]
            for key in ('cube', 'kind', 'leaf', 'cnf_sha256', 'cnf_bytes'):
                assert r[key] == e[key]
            if r['kind'] == 'leaf':
                assert r['units'] == e['units']
        independent = True
    return {'status': 'CANARY_V2_RECEIPT_METADATA_AND_TERMINAL_CHECKS_PASS',
            'worker_pin': PIN, 'inputs_sha256': INPUT, 'manifest_sha256': MANIFEST,
            'batches': summaries, 'items': 394, 'covers': 2, 'leaves': 392,
            'carried': sum(bool(r.get('carried')) for r in all_receipts), 'nodes_with_accepted_receipts': nodes,
            'proof_bytes_reported': sum(r['proof']['bytes'] for r in all_receipts),
            'independent_formula_identity_checked': independent,
            'canary_fleet_deleted': True, 'canary_controller_terminated': True,
            'main_launched_before_canary_completed': True,
            'canary_accepted': False, 'full_campaign_verified': False, 'lean_evidence_discharged': False,
            'limitations': ['Pending independent v2 CNF reconstruction on cloud builder (stopped at snapshot).'] if not independent else [],
            'scope': 'Receipt metadata and archived operational evidence; no rerun of solver/checker, no independent retained-proof byte hashing, and no Lean admission.'}


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--inputs', required=True, type=Path)
    p.add_argument('--expected', type=Path)
    a = p.parse_args()
    print(json.dumps(audit(Path(__file__).resolve().parent, a.inputs, a.expected), indent=2))
