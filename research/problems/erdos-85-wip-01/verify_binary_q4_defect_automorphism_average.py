#!/usr/bin/env python3
"""Exact Aut(D) convex decomposition of A/4 in the actual q4 control.

Verification uses only the eight permutations below, not their discovery
by graph-isomorphism enumeration. This proves no compactness claim for D
and no assertion about q>=8 or connected defect.
"""

from binary_q4_fixed_free_disconnected_control import A_EDGES, adjacency

PERMUTATIONS = (
    (2, 0, 7, 11, 1, 8, 9, 15, 6, 13, 3, 5, 4, 10, 12, 14),
    (2, 0, 7, 10, 1, 11, 8, 15, 5, 6, 13, 3, 4, 9, 12, 14),
    (1, 4, 0, 11, 12, 8, 9, 2, 6, 13, 3, 5, 14, 10, 15, 7),
    (1, 4, 0, 10, 12, 11, 8, 2, 5, 6, 13, 3, 14, 9, 15, 7),
    (9, 5, 3, 7, 10, 0, 4, 8, 15, 2, 1, 12, 6, 14, 11, 13),
    (5, 10, 9, 7, 6, 0, 4, 3, 15, 2, 1, 12, 11, 14, 13, 8),
    (9, 5, 3, 2, 10, 1, 12, 8, 7, 0, 4, 14, 6, 15, 11, 13),
    (5, 10, 9, 2, 6, 1, 12, 3, 7, 0, 4, 14, 11, 15, 13, 8),
)


def main():
    a = adjacency(A_EDGES)
    n = len(a)
    assert n == 16
    assert all(len(a[u]) == 4 and u not in a[u] for u in range(n))
    assert all((v in a[u]) == (u in a[v]) for u in range(n) for v in range(n))
    assert all(len(a[u] & a[v]) <= 1
               for u in range(n) for v in range(u))
    d = [{v for v in range(n) if v != u and not (a[u] & a[v])}
         for u in range(n)]
    assert all(len(row) == 3 for row in d)
    assert len(PERMUTATIONS) == len(set(PERMUTATIONS)) == 8
    for p in PERMUTATIONS:
        assert sorted(p) == list(range(n))
        assert all(p[u] in a[u] for u in range(n))
        assert all((v in d[u]) == (p[v] in d[p[u]])
                   for u in range(n) for v in range(n))
        assert any((v in a[u]) != (p[v] in a[p[u]])
                   for u in range(n) for v in range(n))
    # Convention: P_sigma[u,v] = 1 iff v=sigma(u).
    assert all(sum(p[u] == v for p in PERMUTATIONS) == 2 * int(v in a[u])
               for u in range(n) for v in range(n))
    print('verified: simple 4-regular C4-free graph on16 vertices')
    print('verified: eight A-supported automorphisms of D, none of A')
    print('verified: sum(P_sigma)=2A, hence mean(P_sigma)=A/4')


if __name__ == '__main__':
    main()
