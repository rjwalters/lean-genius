#!/usr/bin/env python3
"""Exact q16 internal control; no incidence B or exterior T is constructed."""

from itertools import combinations


def construct():
    """Index (x,i) in F2^4 x {0,1,2} by 3*x+i."""
    steps = (1, 2, 4, 8, 15)
    generators = (3, 5, 9)
    permutations = ((1, 0, 2), (2, 1, 0), (0, 2, 1))
    d = [{3 * (x ^ s) + j for s in steps for j in range(3)}
         for x in range(16) for _ in range(3)]
    h = [{3 * (x ^ s) + p[i] for s, p in zip(generators, permutations)}
         for x in range(16) for i in range(3)]
    return h, d


def closed_neighborhood_binary_rank(d):
    basis = {}
    for i, neighbors in enumerate(d):
        row = (1 << i) | sum(1 << j for j in neighbors)
        while row:
            pivot = row.bit_length() - 1
            if pivot in basis:
                row ^= basis[pivot]
            else:
                basis[pivot] = row
                break
    return len(basis)


def check():
    h, d = construct()
    assert len(h) == len(d) == 48
    for a in range(48):
        assert len(d[a]) == 15 and len(h[a]) == 3
        assert a not in d[a] | h[a]
        assert not (d[a] & h[a])  # diag(HD)=0, stronger than evenness.
        for b in range(48):
            assert (b in d[a]) == (a in d[b])
            assert (b in h[a]) == (a in h[b])
            assert len(h[a] & d[b]) == len(d[a] & h[b])
            if a != b:
                assert len(h[a] & h[b]) <= (0 if b in d[a] else 1)
            if b in d[a]:
                assert not (d[a] & d[b])
    seen, pending = {0}, [0]
    while pending:
        for b in d[pending.pop()] - seen:
            seen.add(b)
            pending.append(b)
    assert len(seen) == 48
    cycle = [3 * x for x in (0, 1, 3, 7, 15)]
    for i, j in combinations(range(5), 2):
        assert (cycle[j] in d[cycle[i]]) == ((j - i) in (1, 4))
    assert closed_neighborhood_binary_rank(d) == 38
    # This is the required off-diagonal BB^T support, not an actual B.
    residual = [{b for b in range(48) if b != a and b not in d[a]
                 and not (h[a] & h[b])} for a in range(48)]
    assert all(len(row) == 26 for row in residual)
    print("PASS: D connected triangle-free nonbipartite 15-regular on48; rank_F2(D+I)=38")
    print("H cubic C4-free; HD=DH; diag(HD)=0; H^2 zero on D-edges")
    print("Residual incidence support is26-regular; no B or T asserted")


if __name__ == '__main__':
    check()
