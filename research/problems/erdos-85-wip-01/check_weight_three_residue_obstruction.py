#!/usr/bin/env python3
"""Check exact model inputs to the modulo-three completion obstruction.

This verifies the finite carrier data, not a guessed exterior adjacency.
The universal implication from these data is proved in the companion audit.
"""

from itertools import combinations


def check():
    q, order, n = 16, 48, 13
    h = [{(s - x) % order for s in (1, 3, 7)} for x in range(order)]
    lengths = ((7, 8, 15), (5, 9, 14), (3, 10, 13), (1, 11, 12))
    generic = [frozenset((x, (x + a) % order, (x + c) % order))
               for a, b, c in lengths for x in range(order)]
    special = [frozenset((x, x + q, x + 2 * q)) for x in range(q)]
    blocks = generic + special
    assert len(blocks) == len(set(blocks)) == q * n
    assert all(len(block) == 3 for block in blocks)
    assert len(generic) == 192 and len(special) == q
    assert all(sum(x in block for block in special) == 1 for x in range(order))
    assert all(sum(block) % 3 == 1 for block in generic)
    assert all(sum(block) % 3 == 0 for block in special)
    assert sum(range(order)) % 3 == 0
    assert all(sum(h[x]) % 3 == 2 for x in range(order))
    incidence = [{f for f, block in enumerate(blocks) if x in block} for x in range(order)]
    assert all(len(row) == n for row in incidence)
    for x, y in combinations(range(order), 2):
        defect = q < (y - x) % order < 2 * q
        assert len(h[x] & h[y]) + len(incidence[x] & incidence[y]) == 1 - defect
    for block in blocks:
        forbidden = set.union(*(h[x] for x in block))
        assert len(forbidden) == 9
        allowed = set(range(order)) - forbidden
        assert len(allowed) == 3 * n
        assert sum(allowed) % 3 == 0
    # Any integral exact-cover column has n edges and n-k generic blocks.
    possible_special_degrees = [k for k in range(n + 1) if (n - k) % 3 == 0]
    assert possible_special_degrees == [1, 4, 7, 10, 13]
    # Symmetry gives total special incidence |Z|*n = |F|, hence average one.
    assert len(special) * n == len(blocks)
    print("PASS: 208 exact column residue inputs; special degrees in {1,4,7,10,13}; average forced to 1")
    print("Conclusion requires the proof in the companion audit: connected exterior Gram completion impossible")


if __name__ == "__main__":
    check()
