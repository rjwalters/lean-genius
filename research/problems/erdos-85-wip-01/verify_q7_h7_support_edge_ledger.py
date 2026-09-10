"""Finite arithmetic checks accompanying the paper H7 edge ledger.

This does not formalize the actual-graph counting argument or enumerate
H7 graphs. Small explicit witnesses realize only induced-graph conditions.
"""
from itertools import combinations, product


def main():
    local = {}
    for t in range(3):
        local[t] = [(n0, n1, n2) for n0, n1, n2 in product(range(8), repeat=3)
                    if n0+n1+n2 == 7-t and n1+2*n2 == 7]
        assert local[t] == [(n0, 7-2*n0-2*t, n0+t) for n0 in range(4-t)]
        assert max(row[0] for row in local[t]) == 3-t
    assert [a for a in range(25) if 0 <= 49-4*a <= 28 and 0 <= 2*a <= 21] == list(range(6, 11))

    # Sorted degree sequences for the putative a=10 subcubic graph.
    sequences = [d for d in product(range(4), repeat=7)
                 if tuple(sorted(d)) == d and sum(d) == 20]
    assert sequences == [(2, 3, 3, 3, 3, 3, 3)]
    assert 6 > 2  # Some degree3 vertex is not adjacent to the degree2 vertex.
    assert 1+3+(3*(3-1)-2*1) == 8 > 7

    for a in range(6, 10):
        e00, e01, e02, e11, e12, e22 = a, 49-4*a, 2*a, 4*a-14, 63-4*a, a+21
        assert 2*e00+e01+e02 == 7*7
        assert e01+2*e11+e12 == 14*6
        assert e02+e12+2*e22 == 21*5
        assert e01+2*e02 == 7*7
        assert 2*e11+2*e12 == 14*7
        assert e12+4*e22 == 21*7
        assert e02 == 2*e00 and e12 == e01+14 and 2*e22 == e02+42
        assert sum([e00, e01, e02, e11, e12, e22]) == 119
        print('PASS edge ledger', a, ':', [e00, e01, e02, e11, e12, e22])

    cycle = [(i, (i+1) % 7) for i in range(7)]
    examples = {
        6: cycle[:-1],
        7: cycle,
        8: cycle+[(0, 2)],
        # Triangle0,1,2 and three subdivided spokes from vertex3.
        9: [(0, 1), (1, 2), (2, 0), (3, 4), (4, 0),
            (3, 5), (5, 1), (3, 6), (6, 2)],
    }
    for a, edges in examples.items():
        assert len(set(tuple(sorted(e)) for e in edges)) == a
        neighbors = [set() for _ in range(7)]
        for u, v in edges:
            assert 0 <= u < 7 and 0 <= v < 7 and u != v
            neighbors[u].add(v)
            neighbors[v].add(u)
        assert max(map(len, neighbors)) <= 3
        assert all(len(neighbors[u] & neighbors[v]) <= 1 for u, v in combinations(range(7), 2))
        print('PASS small induced-graph witness with', a, 'edges')
    print('Paper-level universal H7 condition: 6 <= e00 <= 9; no sector exclusion.')


if __name__ == '__main__':
    main()
