#!/usr/bin/env python3
"""Exact q16 internal control and packing certificate excluding incidence B."""

from itertools import combinations, combinations_with_replacement


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
    # Six full block classes form a triangle-free subgraph too large for
    # a triangle decomposition of the residual graph.
    r = {3, 5, 7, 9, 11, 13}
    assert all((a ^ b) not in r for a in r for b in r)
    xgraph = [{b for b in range(48) if (a//3) ^ (b//3) in r}
              for a in range(48)]
    for a in range(48):
        assert len(xgraph[a]) == 18
        assert xgraph[a] <= residual[a]
        for b in xgraph[a]:
            assert a in xgraph[b]
            assert not (xgraph[a] & xgraph[b])
    residual_edges = sum(map(len, residual)) // 2
    x_edges = sum(map(len, xgraph)) // 2
    assert residual_edges == 624 and x_edges == 432
    assert residual_edges % 3 == 0
    assert x_edges > 2 * (residual_edges // 3)
    signs = [1 if (a//3) % 2 == 0 else -1 for a in range(48)]
    assert sum(signs) == 0
    assert all(sum(signs[b] for b in h[a]) == -3*signs[a] for a in range(48))
    assert all(sum(signs[b] for b in d[a]) == 3*signs[a] for a in range(48))
    assert (15 - 3 - 9)*48 == 144 < 208
    # All three-shift quotient multisets, including zero and repetitions;
    # the audit gives the subspace proof independent of this finite check.
    for generators in combinations_with_replacement(range(16), 3):
        witnesses = [k for k in range(1, 16) if k.bit_count() in (1, 2)
                     and len({(k & s).bit_count() % 2 for s in generators}) == 1]
        assert witnesses
    print("PASS: D connected triangle-free nonbipartite 15-regular on48; rank_F2(D+I)=38")
    print("H cubic C4-free; HD=DH; diag(HD)=0; H^2 zero on D-edges")
    print("Residual L:624 edges; triangle-free X subset:432 edges")
    print("NO B:208 required triangles cover at most416 X-edges, below432")


if __name__ == '__main__':
    check()
