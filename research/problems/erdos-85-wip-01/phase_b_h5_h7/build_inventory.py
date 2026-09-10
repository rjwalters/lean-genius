"""Read-only input audit; emits only small inventory metadata, never runs SAT."""
import hashlib
import itertools
import json
from pathlib import Path
import subprocess

REPO = Path('/Users/rwalters/GitHub/lean-genius/.codex/worktrees/erdos85-sol2-integration')
ROOT = REPO / 'research/problems/erdos-85-wip-01'
OUT = Path(__file__).resolve().parent
CAMPAIGN = Path('/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/campaign-20260825.noindex')

def digest(path):
    h = hashlib.sha256()
    with path.open('rb') as f:
        for block in iter(lambda: f.read(1024*1024), b''):
            h.update(block)
    return h.hexdigest()

def pin(path):
    return {'path': str(path), 'sha256': digest(path), 'bytes': path.stat().st_size}

def source(name):
    p = ROOT / 'sat49' / name
    r = pin(p)
    r['last_change_commit'] = subprocess.check_output(
        ['git', 'log', '-1', '--format=%H', '--', str(p.relative_to(REPO))], cwd=REPO, text=True).strip()
    return r

def main():
    parent_path = ROOT / 'closure-inventory-evidence/h7-parent.json'
    capacity_path = ROOT / 'q7_h7_universal_singleton_capacity.json'
    parent = json.loads(parent_path.read_text())
    capacity = json.loads(capacity_path.read_text())
    h7_base = CAMPAIGN / 'h7canon/compact_8bc9b8f1.cnf'
    assert digest(h7_base) == parent['base_sha256']
    h7_prefix = hashlib.sha256()
    h7_prefix_bytes = 0
    headers = 0
    with h7_base.open('rb') as f:
        for raw in f:
            if raw.lstrip().startswith(b'p cnf'):
                headers += 1
                raw = f"p cnf {parent['variables']} {parent['cube_clauses']}\n".encode()
            h7_prefix.update(raw)
            h7_prefix_bytes += len(raw)
    assert headers == 1
    edges = list(itertools.combinations(range(7), 2))
    edge_index = {e: i for i, e in enumerate(edges)}
    targets = {r['mask']: r for r in capacity}
    assert len(targets) == 43
    for row in capacity:
        assert row['mask'] == sum(1 << edge_index[tuple(e)] for e in row['edges'])
    mapping = []
    for job in parent['jobs']:
        units = ''.join(f'{lit} 0\n' for lit in job['units']).encode()
        h = h7_prefix.copy()
        h.update(units)
        assert h.hexdigest() == job['cnf_sha256']
        assert h7_prefix_bytes + len(units) == job['cnf_bytes']
        present = [e for i, e in enumerate(edges) if job['mask'] >> i & 1]
        found = None
        for perm in itertools.permutations(range(7)):
            mask = sum(1 << edge_index[tuple(sorted((perm[a], perm[b])))] for a, b in present)
            if mask in targets:
                found = (perm, targets[mask])
                break
        assert found is not None, job['id']
        perm, row = found
        assert len(present) == row['a'] == job['edge_count']
        assert sorted(tuple(sorted((perm[a], perm[b]))) for a, b in present) == sorted(map(tuple, row['edges']))
        mapping.append({**job, 'sector': 'H7', 'classification_mask': row['mask'],
                        'parent_to_classification_permutation': list(perm),
                        'capacity_excluded': row['excluded'],
                        'capacity_lower': row['lower'], 'capacity_upper': row['upper_bound'],
                        'cnf_path': None, 'requires_materialization': True,
                        'input_hash_status': 'freshly derived from hash-verified base and exact emitter bytes'})
    assert len({r['classification_mask'] for r in mapping}) == 43
    survivors = [r for r in mapping if not r['capacity_excluded']]
    assert [sum(r['edge_count'] == a for r in survivors) for a in range(6, 10)] == [7,12,7,2]
    h7 = {'schema': 'erdos85-phase-b-h7-inventory-v1', 'parent': pin(parent_path),
          'capacity_certificate': pin(capacity_path),
          'generator': source('generate_h7_empty_cube_manifest.py'),
          'base': pin(h7_base), 'base_sha256': parent['base_sha256'], 'variables': parent['variables'],
          'cube_clauses': parent['cube_clauses'], 'mapping': mapping,
          'survivors': survivors,
          'counts': {'all_classes': 43, 'capacity_excluded': 15, 'capacity_survivors': 28,
                     'survivors_with_historical_direct_certificate': sum(r.get('status') == 'certified' for r in survivors)}}
    (OUT / 'h7-inventory.json').write_text(json.dumps(h7, indent=2) + '\n')

    manifest_path = CAMPAIGN / 'cube_jobs_manifest.live-38b15d484b.json'
    assert digest(manifest_path) == '05381a1cf5e80eb480b6e78c4a8dada2573c1cf2f0c55d9ac0bcc4367e3bca76'
    manifest = json.loads(manifest_path.read_text())
    metadata_path = ROOT / 'closure-inventory-evidence/small-high-root-metadata.json'
    metadata = json.loads(metadata_path.read_text())
    hard = {r['id'] for r in metadata['rows'] if r['id'].startswith('h5_') and not r['local_lrat_gz_exists']}
    assert len(hard) == 129
    jobs = []
    bases = {}
    for name, cell in manifest['cells'].items():
        if not name.startswith('h5_'):
            continue
        base = Path(cell['base'])
        assert digest(base) == cell['base_sha256']
        # Match the retained emitter byte-for-byte, hash each distinct header once.
        chosen = [j for j in cell['jobs'] if j['id'] in hard]
        prefixes = {}
        for unit_count in {len(j['units']) for j in chosen}:
            h = hashlib.sha256()
            size = 0
            headers = 0
            with base.open('rb') as f:
                for raw in f:
                    if raw.lstrip().startswith(b'p cnf'):
                        headers += 1
                        raw = f"p cnf {cell['variables']} {cell['base_clauses'] + unit_count}\n".encode()
                    h.update(raw)
                    size += len(raw)
            assert headers == 1
            prefixes[unit_count] = h, size
        bases[name] = {k: v for k, v in cell.items() if k != 'jobs'}
        bases[name]['hash_verified_now'] = True
        for job in chosen:
            prefix, size = prefixes[len(job['units'])]
            h = prefix.copy()
            units = ''.join(f'{lit} 0\n' for lit in job['units']).encode()
            h.update(units)
            jobs.append({**job, 'sector': 'H5', 'cell': name,
                         'cnf_sha256': h.hexdigest(), 'cnf_bytes': size + len(units),
                         'variables': cell['variables'], 'clauses': cell['base_clauses'] + len(job['units']),
                         'input_hash_status': 'freshly derived from hash-verified base and exact emitter bytes',
                         'cnf_path': None, 'requires_materialization': True})
    assert len(jobs) == 129 and {j['id'] for j in jobs} == hard
    h5 = {'schema': 'erdos85-phase-b-h5-inventory-v1', 'manifest': pin(manifest_path),
          'historical_metadata': pin(metadata_path), 'historical_checked_utc': metadata['checked_utc'],
          'generator': source('generate_small_high_cube_jobs.py'),
          'manifest_generator_sha256': manifest['emitter_sha256'],
          'freight_lean_commit': manifest['lean_commit'], 'bases': bases, 'jobs': jobs,
          'counts': {'all_roots': 174, 'historical_direct_certificates': 45, 'conservative_candidates': 129},
          'scope': 'Historical conservative remainder; no claim of fresh absence of later solver results.'}
    (OUT / 'h5-inventory.json').write_text(json.dumps(h5, indent=2) + '\n')
    print(json.dumps({'H5': h5['counts'], 'H7': h7['counts'],
                      'outputs': [pin(OUT / 'h5-inventory.json'), pin(OUT / 'h7-inventory.json')]}))

if __name__ == '__main__':
    main()
