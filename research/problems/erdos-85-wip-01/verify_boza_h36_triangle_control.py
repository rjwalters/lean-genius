#!/usr/bin/env python3
"""Offline regression: Boza H36 refutes generic-even-q triangle identities.

Source: Luis Boza, arXiv:2409.12770v2 (12 June 2026), Section 3,
Lemma 9; https://arxiv.org/pdf/2409.12770v2 identifies H36 as HoG 56942.
Adjacency rows copied 2026-09-06 from:
https://houseofgraphs.org/api/graphs/56942
Graph page: https://houseofgraphs.org/graphs/56942

This actual q=6 graph has connected nonbipartite defect D and connected
E=D minus A, the distance-three graph. Triangle degrees vary along both.
It refutes T2 (triangle sums q+1), AT (At=(q*q+2)/3), and constancy
of triangle degree on far components under generic even-q assumptions.
It does NOT refute their binary-q versions or solve Erdős 85.
No external packages or network needed to verify the stored witness.
"""

from collections import Counter, deque
from itertools import combinations

ROWS = [[1, 2, 3, 4, 5, 6],
 [0, 27, 28, 31, 32, 34],
 [0, 26, 29, 30, 33, 35],
 [0, 5, 10, 14, 20, 25],
 [0, 6, 11, 16, 19, 22],
 [0, 3, 12, 13, 15, 24],
 [0, 4, 17, 18, 21, 23],
 [19, 20, 23, 24, 30, 31],
 [9, 22, 23, 25, 32, 35],
 [8, 21, 24, 25, 33, 34],
 [3, 17, 19, 25, 28, 29],
 [4, 15, 16, 25, 27, 30],
 [5, 13, 16, 21, 31, 35],
 [5, 12, 17, 22, 26, 27],
 [3, 16, 18, 20, 26, 34],
 [5, 11, 18, 24, 29, 32],
 [4, 11, 12, 14, 34, 35],
 [6, 10, 13, 23, 29, 34],
 [6, 14, 15, 21, 26, 28],
 [4, 7, 10, 22, 24, 28],
 [3, 7, 14, 23, 27, 33],
 [6, 9, 12, 18, 31, 33],
 [4, 8, 13, 19, 26, 32],
 [6, 7, 8, 17, 20, 35],
 [5, 7, 9, 15, 19, 34],
 [3, 8, 9, 10, 11, 30],
 [2, 13, 14, 18, 22, 30],
 [1, 11, 13, 20, 28, 33],
 [1, 10, 18, 19, 27, 35],
 [2, 10, 15, 17, 32, 33],
 [2, 7, 11, 25, 26, 31],
 [1, 7, 12, 21, 30, 32],
 [1, 8, 15, 22, 29, 31],
 [2, 9, 20, 21, 27, 29],
 [1, 9, 14, 16, 17, 24],
 [2, 8, 12, 16, 23, 28]]


def distances(adj, start):
    dist = {start: 0}
    queue = deque([start])
    while queue:
        u = queue.popleft()
        for v in adj[u]:
            if v not in dist:
                dist[v] = dist[u] + 1
                queue.append(v)
    return dist



def rank_mod_two(rows):
    """Exact row reduction on bit-packed rows over F2."""
    pivots = {}
    for row in rows:
        value = row
        while value:
            pivot = value.bit_length() - 1
            if pivot not in pivots:
                pivots[pivot] = value
                break
            value ^= pivots[pivot]
    return len(pivots)


def verify():
    q = 6
    n = q*q
    assert len(ROWS) == n
    a = [set(row) for row in ROWS]
    for u, row in enumerate(ROWS):
        assert len(row) == len(a[u]) == q
        assert all(0 <= v < n and v != u and u in a[v] for v in row)
    pairs = list(combinations(range(n), 2))
    assert max(len(a[u] & a[v]) for u, v in pairs) == 1
    # Squaring need not double individual Smith invariant exponents:
    # it can change the count of invariant factors divisible by two.
    packed_a = [sum(1 << v for v in row) for row in a]
    packed_square = [sum((len(a[u] & a[v]) % 2) << v for v in range(n))
                     for u in range(n)]
    assert rank_mod_two(packed_a) == 32
    assert rank_mod_two(packed_square) == 28
    triangles = [(u, v, w) for u, v, w in combinations(range(n), 3)
                 if v in a[u] and w in a[u] & a[v]]
    t = [sum(u in tri for tri in triangles) for u in range(n)]
    d = [{v for v in range(n) if v != u and not a[u] & a[v]}
         for u in range(n)]
    e = [d[u] - a[u] for u in range(n)]
    assert all(len(row) == q-1 for row in d)
    assert len(distances(d, 0)) == len(distances(e, 0)) == n
    # An odd cycle in D is certified by an edge within a BFS parity class.
    dd = distances(d, 0)
    assert any(v in d[u] and dd[u] % 2 == dd[v] % 2 for u, v in pairs)
    for u in range(n):
        da = distances(a, u)
        assert len(da) == n and max(da.values()) == 3
        assert e[u] == {v for v in da if da[v] == 3}
        assert len(e[u]) == 2*t[u]-1
    assert len(triangles) == 32
    assert Counter(t) == {2: 12, 3: 24}
    triangle_sums = Counter(sum(t[u] for u in tri) for tri in triangles)
    assert triangle_sums == {6: 1, 8: 21, 9: 10}
    at = Counter(sum(t[v] for v in row) for row in a)
    assert at == {14: 3, 15: 5, 16: 18, 17: 9, 18: 1}
    assert all(3*value != q*q+2 for value in at)
    assert all(value != q+1 for value in triangle_sums)
    for adj in (d, e):
        assert sum(v in adj[u] and t[u] != t[v] for u, v in pairs) == 30
    # The proved triangle-edge inequality survives this full graph control.
    assert min(t[u]+t[v] for u, v in pairs if v in a[u] and a[u] & a[v]) == q//2+1
    print("verified: simple 6-regular C4-free graph on 36 vertices")
    print("D connected nonbipartite; distance-three E connected")
    print("F2 ranks: A=32, A²=28; individual Smith exponents do not double")
    print("triangle degrees:", dict(sorted(Counter(t).items())))
    print("triangle sums:", dict(sorted(triangle_sums.items())))
    print("At values:", dict(sorted(at.items())))
    print("30 unequal-triangle-degree edges in each of D and E")
    print("generic-even-q T2/AT/far constancy fail; binary q remains open")


if __name__ == "__main__":
    verify()
