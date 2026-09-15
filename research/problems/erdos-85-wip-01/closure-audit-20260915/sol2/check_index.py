"""Read-only audit of the frozen Phase B index against Git-pinned sources."""
import hashlib
import json
from pathlib import Path
import subprocess
from collections import Counter

REPO = '/Users/rwalters/GitHub/lean-genius'
BASE = 'research/problems/erdos-85-wip-01/'
REV = subprocess.check_output(['git', '-C', REPO, 'rev-parse', 'erdos85/integration'], text=True).strip()

def blob(path):
    return subprocess.check_output(['git', '-C', REPO, 'show', f'{REV}:{BASE}{path}'])

raw = blob('phase_b_survivors_20260910.json')
index = json.loads(raw)
assert index['launch_ready'] is False
assert len(index['cases']) == index['total'] == 1416
assert len({r['id'] for r in index['cases']}) == 1416
counts = Counter(r['sector'] for r in index['cases'])
assert counts == index['counts']
sources = {}
for sector, spec in index['sources'].items():
    source = blob(spec['path'])
    assert hashlib.sha256(source).hexdigest() == spec['sha256']
    rows = json.loads(source)[spec['array']]
    refs = [r for r in index['cases'] if r['sector'] == sector]
    assert len(rows) == len(refs) == spec['count']
    assert sorted(r['source_index'] for r in refs) == list(range(len(rows)))
    for ref in refs:
        row = rows[ref['source_index']]
        assert row['id'] == ref['id']
        assert row.get('cnf_sha256') == ref['cnf_sha256']
    sources[sector] = spec

receipt = {
    'status': 'PASS', 'revision': REV,
    'scope': 'Frozen index/source hash and complete ID/index/CNF-hash bijection only; no exclusion proof or solver replay.',
    'index_sha256': hashlib.sha256(raw).hexdigest(),
    'counts': dict(counts), 'total': 1416, 'sources': sources,
    'launch_ready': False,
}
Path(__file__).with_name('index-review.json').write_text(json.dumps(receipt, indent=2)+'\n')
print(json.dumps(receipt, indent=2))

h5 = json.loads(blob(sources['H5']['path']))['jobs']
mapping_receipts = {}
for cell in ('t0', 't1'):
    path = f'phase_b_{cell}_exclusion_mapping/results.json'
    data = blob(path)
    mapping = json.loads(data)
    assert mapping['status'] == 'EXACT_INPUT_MAPPING_ONLY'
    assert mapping['index_sha256'] == receipt['index_sha256']
    assert mapping['h5_inventory_sha256'] == sources['H5']['sha256']
    expected = {r['id'] for r in h5 if r['cell'] == f'h5_{cell}'}
    rows = mapping['rows']
    assert len(rows) == mapping['mapped_count'] == len(expected) == 43
    assert {r['id'] for r in rows} == expected
    for row in rows:
        src = h5[row['source_index']]
        for key in ('id', 'units', 'cnf_sha256', 'cnf_bytes'):
            assert row[key] == src[key], (cell, row['id'], key)
    mapping_receipts[cell] = {
        'source_path': BASE+path,
        'sha256': hashlib.sha256(data).hexdigest(),
        'count': 43,
    }
result = {'status': 'PASS', 'revision': REV,
          'scope': 'Saved H5 T0/T1 mapping identity, units, size and hash join only; no base materialization or mathematical exclusion replay.',
          'index_sha256': receipt['index_sha256'], 'mappings': mapping_receipts}
Path(__file__).with_name('h5-mapping-review.json').write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps(result, indent=2))
