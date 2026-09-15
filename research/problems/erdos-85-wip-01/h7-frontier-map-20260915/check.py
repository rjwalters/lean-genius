"""Join accepted structural H7 scopes to frozen roots; no solver/search replay."""
import hashlib
import itertools
import json
from pathlib import Path

ROOT = Path('/Users/rwalters/GitHub/lean-genius/.codex/worktrees/erdos85-sol2-integration/research/problems/erdos-85-wip-01')
OUT = Path(__file__).parent
PAIRS = list(itertools.combinations(range(7), 2))
pins = {}

def read(path):
    raw = (ROOT / path).read_bytes()
    pins[path] = hashlib.sha256(raw).hexdigest()
    return json.loads(raw)

def edges(mask):
    assert 0 <= mask < (1 << 21)
    return {p for i, p in enumerate(PAIRS) if mask & (1 << i)}

def transport(es, perm):
    assert sorted(perm) == list(range(7))
    return {tuple(sorted((perm[a], perm[b]))) for a, b in es}

def iso(es, target):
    deg = [sum(v in e for e in es) for v in range(7)]
    td = [sum(v in e for e in target) for v in range(7)]
    for perm in itertools.permutations(range(7)):
        if all(deg[v] == td[perm[v]] for v in range(7)) and transport(es, perm) == target:
            return list(perm)
    return None

reviews = {
    'a9': ('q7_h7_a9_closure/review2080/REVIEW2080.json', 2080),
    'a8': ('q7_h7_high_singleton_min3/review-2091.json', 2091),
    'C7': ('q7_h7_a7_cycle_exclusion/review-2117.json', 2117),
    'F9': ('q7_h7_a7_f9_closure/ACCEPTED_REVIEW.json', 2127),
    'F15': ('q7_h7_a6_f15_closure/review-record.json', 2131),
}
for path, rid in reviews.values():
    r = read(path)
    if rid == 2080:
        assert r['review_id'] == rid and r['status'] == 'PASS'
    else:
        assert r['id'] == rid and r['status'] == 'resolved' and r['resolution'].startswith('PASS')

shapes = {
    'C7': {tuple(sorted((i, (i + 1) % 7))) for i in range(7)},
    'F9': {(0,1), (0,2), (0,3), (1,2), (4,5), (4,6), (5,6)},
    'F15': {(0,1), (0,5), (1,5), (2,3), (2,4), (3,4)},
}
# Pin prose specifying the reviewed shapes, as well as the acceptance records.
for path in ['q7_h7_a7_f9_closure/author/CLOSURE.md',
             'q7_h7_a6_f15_closure/source/CLOSURE.md',
             'q7_h7_a7_cycle_exclusion/STATUS.md']:
    pins[path] = hashlib.sha256((ROOT / path).read_bytes()).hexdigest()

index = read('phase_b_survivors_20260910.json')
ref = index['sources']['H7']
inv = read(ref['path'])
assert pins[ref['path']] == ref['sha256']
indexed = {r['id']: r for r in index['cases'] if r['sector'] == 'H7'}
assert len(indexed) == len(inv['survivors']) == 28
rows = []
for offset, r in enumerate(inv['survivors']):
    entry = indexed[r['id']]
    assert entry['source_index'] == offset and entry['cnf_sha256'] == r['cnf_sha256']
    es = edges(r['mask'])
    assert len(es) == r['edge_count']
    assert transport(es, r['parent_to_classification_permutation']) == edges(r['classification_mask'])
    scope = None
    witness = None
    if r['edge_count'] in (8,9):
        scope = 'a' + str(r['edge_count'])
    else:
        for label, target in shapes.items():
            if len(es) == len(target):
                p = iso(es, target)
                if p is not None:
                    assert scope is None
                    scope, witness = label, p
    rows.append(dict(id=r['id'], edge_count=r['edge_count'], mask=r['mask'],
                     cnf_sha256=r['cnf_sha256'], scope=scope,
                     review_id=reviews[scope][1] if scope else None,
                     parent_to_reviewed_shape=witness,
                     status='IN_ACCEPTED_STRUCTURAL_SCOPE' if scope else 'NOT_COVERED_BY_SELECTED_SCOPES'))

excluded = [r['id'] for r in rows if r['scope']]
residual = [r['id'] for r in rows if not r['scope']]
assert len(set(excluded + residual)) == 28 and not set(excluded) & set(residual)
result = dict(status='PASS_SCOPE_JOIN', rows=rows, covered=excluded, residual=residual,
              counts=dict(total=28, covered=len(excluded), residual=len(residual)),
              scope='Conditional join to five accepted paper/computation exclusions. Does not replay exclusions, supply Lean proofs, or modify solver queue. Residual means not covered by these selected scopes.',
              source_pins=pins)
(OUT / 'results.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(dict(counts=result['counts'], covered=excluded, residual=residual), indent=2))
