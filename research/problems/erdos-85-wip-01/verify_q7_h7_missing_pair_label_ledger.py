"""Exact small high-label ledger; no full H7 label assignment or graph search."""
from itertools import combinations, product
from collections import Counter

pairs = list(combinations(range(7), 2))
# A three-edge graph has one of these five degree profiles, which distinguish its shape.
shapes = {
    (0, 1, 1, 1, 1, 1, 1): ('3K2', set(range(7))),
    (0, 0, 1, 1, 1, 1, 2): ('P3+K2', set(range(1, 6))),
    (0, 0, 0, 1, 1, 2, 2): ('P4', set(range(2, 5))),
    (0, 0, 0, 1, 1, 1, 3): ('K1,3', set(range(2, 6))),
    (0, 0, 0, 0, 2, 2, 2): ('K3', {3}),
}
local = {}
for d in range(4):
    allocations = [(a, b) for a, b in product(range(3), repeat=2) if a + b == 1 + d]
    local[d] = {int(a == 2) + int(b == 2) for a, b in allocations}
assert local == {0: {0}, 1: {0, 1}, 2: {1}, 3: {2}}
counts = Counter()
for edges in combinations(pairs, 3):
    degree = [0] * 7
    for u, v in edges:
        degree[u] += 1
        degree[v] += 1
    profile = tuple(sorted(degree))
    assert profile in shapes
    name, expected = shapes[profile]
    possible = {sum(terms) for terms in product(*(local[d] for d in degree))}
    assert possible == expected
    assert sum(1 + d for d in degree) == 13
    counts[name] += 1
assert dict(counts) == {'K1,3': 140, 'P4': 420, 'P3+K2': 630, 'K3': 35, '3K2': 105}
assert sum(counts.values()) == 1330
for _, (name, possible) in shapes.items():
    print(name, 'scalar s values', sorted(possible), 'shape A intersection', sorted(possible & {0, 1, 2}),
          'shape B intersection', sorted(possible & {0, 1, 2, 3}))
assert not (shapes[(0, 0, 0, 0, 2, 2, 2)][1] & {0, 1, 2})
print('PASS 1330 three-edge high-label graphs and exact two-singleton incidence arithmetic.')
print('Scalar possibilities do not assert compatible high labels, projectors, or full graph realizations.')
