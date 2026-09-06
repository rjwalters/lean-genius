#!/usr/bin/env python3
"""Exact checks for the weight-three internal model and q16 partial graph.

Standard library only. This does not provide exterior adjacency or a regular
ambient completion. The generic internal proof is in the companion audit.
"""

from collections import Counter
from itertools import combinations


def internal(q):
    assert q >= 8 and q % 2 == 0
    order = 3 * q
    h = [{(s - x) % order for s in (1, 3, 7)} for x in range(order)]
    d = [
        {y for y in range(order) if q < (y - x) % order < 2 * q}
        for x in range(order)
    ]
    for x in range(order):
        assert len(h[x]) == 3 and x not in h[x]
        assert len(d[x]) == q - 1 and x not in d[x]
        for y in range(order):
            assert (y in h[x]) == (x in h[y])
            assert (y in d[x]) == (x in d[y])
            expected = 3 if x == y else int((y - x) % order in
                                             {2, 4, 6, order-2, order-4, order-6})
            assert len(h[x] & h[y]) == expected
            assert len(h[x] & d[y]) == len(d[x] & h[y])
            if y in d[x]:
                assert not (h[x] & h[y])
                assert not (d[x] & d[y])
    reached, todo = {0}, [0]
    while todo:
        for y in d[todo.pop()] - reached:
            reached.add(y)
            todo.append(y)
    assert len(reached) == order
    cycle = [0, q + 1, 2 * q + 2, 3, q + 4]
    assert len(set(cycle)) == 5
    for i, j in combinations(range(5), 2):
        assert (cycle[j] in d[cycle[i]]) == ((j - i) in (1, 4))
    # Uniform parity obstruction to a symmetric integral cross completion.
    witness = q // 2 + 1
    assert len(h[witness] & d[witness]) == 1
    # Check the one-reflection identity for every odd parameter. Linearity
    # then yields the three-reflection family certificate in the audit.
    for s in range(1, order, 2):
        for x in range(order):
            points = [x, (x + q//2) % order, (x + q) % order]
            assert sum((s-v) % order in d[v] for v in points) == 1
    return h, d


def main():
    # Sample checks of a proved formula, not enumeration of graphs.
    for q in (10, 12, 16, 32):
        internal(q)
    q = 16
    order = 3 * q
    h, d = internal(q)
    difference_triples = [(7, 8, 15), (5, 9, 14), (3, 10, 13), (1, 11, 12)]
    assert all(a + b == c for a, b, c in difference_triples)
    assert sorted([2, 4, 6] + [v for t in difference_triples for v in t]) == list(range(1, 16))
    blocks = [frozenset((x, (x+a) % order, (x+c) % order))
              for a, _, c in difference_triples for x in range(order)]
    blocks += [frozenset((x, x+q, x+2*q)) for x in range(q)]
    assert len(blocks) == len(set(blocks)) == q * (q-3)
    assert all(len(block) == 3 for block in blocks)
    b = [{f for f, block in enumerate(blocks) if x in block} for x in range(order)]
    assert all(len(row) == q-3 for row in b)
    for x in range(order):
        for y in range(order):
            assert len(h[x] & h[y]) + len(b[x] & b[y]) == (
                (q-1) * (x == y) + 1 - (y in d[x]))
    ambient = [h[x] | {order+f for f in b[x]} for x in range(order)]
    ambient += [set(block) for block in blocks]
    assert len(ambient) == q*q
    for x in range(q*q):
        assert x not in ambient[x]
        for y in ambient[x]:
            assert x in ambient[y]
    checked = 0
    for x, y in combinations(range(q*q), 2):
        assert len(ambient[x] & ambient[y]) <= 1
        checked += 1
    degrees = Counter(map(len, ambient))
    assert degrees == {16: 48, 3: 208}
    witness = 9
    selected = sorted(b[witness])
    demands = [1 - len(h[witness] & blocks[f]) for f in selected]
    assert len(selected) == 13
    assert set(demands) <= {0, 1}
    assert sum(demands) == 11
    # If BT=J-HB, this sum is sum(T[g,f] for g,f in selected).
    # Symmetric integer T with zero diagonal makes that sum even.
    print(f"PASS: q16 C Gram, triangle-free connected D, HD=DH; {checked} ambient pairs")
    print(f"Partial graph degrees: {dict(sorted(degrees.items()))}; no exterior completion claimed")
    print(f"Cross-parity certificate at C vertex {witness}: labels={selected}, demands={demands}, sum=11 (odd)")


if __name__ == "__main__":
    main()
