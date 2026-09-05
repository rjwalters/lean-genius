#!/usr/bin/env python3
"""Verify a q=8, m=3 internal-selector relaxation countermodel.

K is a formal internal selector graph on one 24-label component and D is a
connected nonbipartite 7-regular formal defect component.  K is not asserted
to be the canonical Baer operator `Omega triangle (D minus T)`.  The checks retain
the exact internal consequences of C4-freeness: K is cubic and linear
(codegree at most one), and every D-edge has disjoint K-neighborhoods.
"""

from __future__ import annotations

import hashlib
import json


K_EDGES = [(0,2),(0,19),(0,23),(1,10),(1,19),(1,20),(2,5),(2,13),
    (3,14),(3,15),(3,21),(4,6),(4,21),(4,22),(5,13),(5,21),
    (6,9),(6,12),(7,10),(7,18),(7,23),(8,14),(8,16),(8,22),
    (9,11),(9,15),(10,11),(11,13),(12,16),(12,20),(14,18),
    (15,17),(16,19),(17,20),(17,22),(18,23)]

D_EDGES = [(0,2),(0,3),(0,10),(0,11),(0,12),(0,17),(0,19),
    (1,14),(1,15),(1,19),(1,20),(1,21),(1,22),(1,23),
    (2,3),(2,15),(2,16),(2,17),(2,20),(2,22),(3,12),(3,13),
    (3,16),(3,20),(3,22),(4,13),(4,15),(4,16),(4,19),(4,20),
    (4,21),(4,23),(5,12),(5,15),(5,16),(5,17),(5,18),(5,19),
    (5,22),(6,7),(6,10),(6,13),(6,14),(6,18),(6,19),(6,23),
    (7,10),(7,15),(7,19),(7,20),(7,21),(7,22),(8,11),(8,14),
    (8,15),(8,20),(8,21),(8,22),(8,23),(9,14),(9,15),(9,19),
    (9,20),(9,21),(9,22),(9,23),(10,11),(10,12),(10,14),
    (10,16),(11,12),(11,13),(11,17),(11,18),(12,13),(12,18),
    (13,14),(13,18),(14,18),(16,21),(16,23),(17,18),(17,21),
    (17,23)]


def neighborhoods(edges: list[tuple[int, int]], order: int) -> list[set[int]]:
    result = [set() for _ in range(order)]
    for x, y in edges:
        assert 0 <= x < y < order
        result[x].add(y)
        result[y].add(x)
    return result


def connected(neighbors: list[set[int]]) -> bool:
    seen = {0}
    stack = [0]
    while stack:
        x = stack.pop()
        for y in neighbors[x] - seen:
            seen.add(y)
            stack.append(y)
    return len(seen) == len(neighbors)


def main() -> int:
    order, q, m = 24, 8, 3
    k_neighbors = neighborhoods(K_EDGES, order)
    d_neighbors = neighborhoods(D_EDGES, order)
    assert all(len(row) == m for row in k_neighbors)
    assert all(len(row) == q - 1 for row in d_neighbors)
    assert connected(d_neighbors)
    assert all(len(k_neighbors[x] & k_neighbors[y]) <= 1
        for x in range(order) for y in range(x + 1, order))
    assert all(not (k_neighbors[x] & k_neighbors[y]) for x, y in D_EDGES)
    triangle = next((x, y, z)
        for x in range(order) for y in d_neighbors[x] if x < y
        for z in d_neighbors[x] & d_neighbors[y] if y < z)
    payload = json.dumps({"D": D_EDGES, "K": K_EDGES},
        sort_keys=True, separators=(",", ":")).encode()
    print(json.dumps({
        "D_connected": True,
        "D_degree": q - 1,
        "D_triangle": triangle,
        "K_degree": m,
        "K_max_codegree": max(len(k_neighbors[x] & k_neighbors[y])
            for x in range(order) for y in range(x + 1, order)),
        "D_edges_have_disjoint_K_neighborhoods": True,
        "model_sha256": hashlib.sha256(payload).hexdigest(),
        "order": order,
    }, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
