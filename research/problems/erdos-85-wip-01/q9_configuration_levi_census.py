#!/usr/bin/env python3
"""Find vertex-transitive Levi candidates for the q=9 triangular shadow.

A symmetric 80_3 linear configuration has a connected cubic bipartite Levi
graph on 160 vertices.  If its point graph is C4-free, the Levi graph has no
6- or 8-cycle, hence has girth at least 10.  Conversely, girth at least 10
ensures that the point graph has no C4.

The input and pin are the same PSV graph6 conversion used by
q9_cubic_shadow_census.py.  For every surviving order-160 graph, this script
also constructs one 80-point graph and verifies degree 6, C4-freeness, and the
exact census of 80 line triangles.
"""

from __future__ import annotations

import argparse
import hashlib
from collections import Counter, deque
from itertools import combinations
from pathlib import Path

import networkx as nx


EXPECTED_SHA256 = "4bac89beec1465265318266117c38a2c1680e73a21efd322411207cef5313088"
EXPECTED_ORDINALS = [41, 42, 43, 44, 53, 56, 62, 63, 64, 66, 75, 76, 80, 84, 100, 101, 104]


def decode(line: bytes) -> nx.Graph:
    return (
        nx.from_sparse6_bytes(line)
        if line.startswith(b":")
        else nx.from_graph6_bytes(line)
    )


def girth(graph: nx.Graph) -> int | None:
    best = len(graph) + 1
    for root in graph:
        distance = {root: 0}
        parent = {root: None}
        queue = deque([root])
        while queue:
            u = queue.popleft()
            for v in graph[u]:
                if v not in distance:
                    distance[v] = distance[u] + 1
                    parent[v] = u
                    queue.append(v)
                elif parent[u] != v:
                    best = min(best, distance[u] + distance[v] + 1)
    return None if best == len(graph) + 1 else best


def point_graph(levi: nx.Graph) -> nx.Graph:
    points, lines = nx.bipartite.sets(levi)
    if len(points) != 80 or len(lines) != 80:
        raise AssertionError((len(points), len(lines)))
    point_graph = nx.Graph()
    point_graph.add_nodes_from(points)
    for line in lines:
        neighbors = list(levi[line])
        assert len(neighbors) == 3
        point_graph.add_edges_from(combinations(neighbors, 2))
    return point_graph


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("census", type=Path)
    args = parser.parse_args()
    raw = args.census.read_bytes()
    digest = hashlib.sha256(raw).hexdigest()
    if digest != EXPECTED_SHA256:
        raise SystemExit(
            f"unexpected census SHA-256: {digest}; expected {EXPECTED_SHA256}"
        )

    order_ordinal = 0
    bipartite_count = 0
    survivors = []
    for line_number, raw_line in enumerate(raw.splitlines(), start=1):
        encoded = raw_line.strip()
        if not encoded:
            continue
        graph = decode(encoded)
        if len(graph) != 160:
            continue
        order_ordinal += 1
        assert nx.is_connected(graph)
        assert set(dict(graph.degree()).values()) == {3}
        if not nx.is_bipartite(graph):
            continue
        bipartite_count += 1
        graph_girth = girth(graph)
        if graph_girth is None or graph_girth < 10:
            continue

        triangular = point_graph(graph)
        assert len(triangular) == 80
        assert set(dict(triangular.degree()).values()) == {6}
        assert all(
            len(nx.common_neighbors(triangular, x, y)) <= 1
            for x, y in combinations(triangular, 2)
        )
        triangle_count = sum(nx.triangles(triangular).values()) // 3
        assert triangle_count == 80
        survivors.append((order_ordinal, line_number, graph_girth, nx.diameter(graph)))

    ordinals = [entry[0] for entry in survivors]
    assert order_ordinal == 104
    assert bipartite_count == 94
    assert ordinals == EXPECTED_ORDINALS, (ordinals, EXPECTED_ORDINALS)

    print(f"sha256 {digest}")
    print(f"order_160_total {order_ordinal}")
    print(f"order_160_bipartite {bipartite_count}")
    print(f"girth_at_least_10 {len(survivors)}")
    print("ordinal source_line girth diameter")
    for entry in survivors:
        print(*entry)


if __name__ == "__main__":
    main()
