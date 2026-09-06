#!/usr/bin/env python3
"""Check the C-shore construction; this does not construct an ambient graph."""

import argparse
from itertools import combinations


def check(q: int) -> dict:
    assert q >= 8 and q % 2 == 0
    size, n = 2 * q, q - 2
    vertices = set(range(size))
    h_steps = {1, size - 1}
    k_steps = {2, size - 2}
    d_steps = (set(range(1, size, 2)) - h_steps) | {q}
    l_steps = (vertices - {0}) - d_steps - k_steps

    def graph(steps):
        assert 0 not in steps and {(-s) % size for s in steps} == steps
        return [{(v + s) % size for s in steps} for v in range(size)]

    h, k, d, l = map(graph, (h_steps, k_steps, d_steps, l_steps))
    for a in range(size):
        assert [len(g[a]) for g in (h, k, d, l)] == [2, 2, q - 1, n]
        assert d[a] | k[a] | l[a] == vertices - {a}
        assert not (d[a] & k[a] or d[a] & l[a] or k[a] & l[a])
        for b in range(size):
            assert len(h[a] & h[b]) == 2 * (a == b) + (b in k[a])
            # HD=DH and HL=LH, directly from adjacency lists.
            assert len(h[a] & d[b]) == len(d[a] & h[b])
            assert len(h[a] & l[b]) == len(l[a] & h[b])

    reached, pending = {0}, [0]
    while pending:
        for b in d[pending.pop()] - reached:
            reached.add(b)
            pending.append(b)
    assert reached == vertices

    # B is the vertex/edge incidence matrix of the simple selector graph L.
    edges = [(a, b) for a in range(size) for b in l[a] if a < b]
    b_rows = [{j for j, edge in enumerate(edges) if a in edge}
              for a in range(size)]
    assert len(edges) == q * n
    for a in range(size):
        assert len(b_rows[a]) == n
        for b in range(size):
            gram = len(b_rows[a] & b_rows[b])
            assert gram == n * (a == b) + (b in l[a])
            assert len(h[a] & h[b]) + gram == (q - 1) * (a == b) + 1 - (b in d[a])

    triangle = [0, q, 3]
    assert all(b in d[a] for a, b in combinations(triangle, 2))
    holes = [h[c] for c in triangle]
    companions = [l[c] for c in triangle]
    assert len(set.union(*holes)) == 6
    x = vertices - set.union(*holes)
    pair_counts = []
    for i, j in combinations(range(3), 2):
        delta = len(companions[i] & d[triangle[j]])
        p = len(companions[i] & companions[j])
        gamma = len(companions[i] & k[triangle[j]])
        cross = sum(b in l[a] for a in holes[i] for b in holes[j])
        assert delta + p + gamma == n and cross == gamma
        pair_counts.append((delta, p, gamma))
    assert pair_counts == [(2, n - 4, 2), (n - 3, 2, 1), (n - 4, 4, 0)]
    t = len(set.intersection(*companions))
    assert set.intersection(*companions) == {4}
    occupancy = [sum(sum(v in r for r in companions) == j
                     for v in vertices - set(triangle)) for j in range(4)]
    total_delta = sum(row[0] for row in pair_counts)
    total_gamma = sum(row[2] for row in pair_counts)
    assert occupancy == [2 * n + 1 - total_delta - total_gamma - t,
                         2 * total_delta + 2 * total_gamma + 3 * t - 3 * n,
                         3 * n - total_delta - total_gamma - 3 * t, t]
    assert occupancy == [2, n - 1, n - 1, 1]
    internal_edges = sum(a in x and b in x for a, b in edges)
    assert internal_edges == n * (n - 4) + 3

    # This defect lift is disconnected; it is not an ambient extension.
    edge_index = {edge: i for i, edge in enumerate(edges)}
    lifted = []
    for a, b in edges:
        neighbors = {edge_index[tuple(sorted(((a + s) % size, (b + s) % size)))]
                     for s in d_steps}
        assert len(neighbors) == q - 1
        lifted.append(neighbors)
    for i, (a, b) in enumerate(edges):
        assert i not in lifted[i]
        counts = [0] * size
        for j in lifted[i]:
            assert i in lifted[j]
            for v in edges[j]:
                counts[v] += 1
        assert counts == [int(a in d[v]) + int(b in d[v]) for v in range(size)]
    unseen = set(range(len(edges)))
    component_sizes = []
    while unseen:
        root = unseen.pop()
        component, pending = {root}, [root]
        while pending:
            for j in lifted[pending.pop()] - component:
                component.add(j)
                pending.append(j)
        unseen -= component
        component_sizes.append(len(component))
    assert component_sizes == [size] * (n // 2)
    return dict(q=q, pairs=pair_counts, occupancy=occupancy,
                internal_selector_edges=internal_edges,
                defect_lift_components=len(component_sizes))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("q", nargs="*", type=int, default=[8, 10, 12, 16, 32, 64])
    args = parser.parse_args()
    for q in args.q:
        print(check(q))
