#!/usr/bin/env python3
"""Exact edge-repair test after deleting the ten absolute points of ER_9.

The canonical 81-vertex induced subgraph has degree profile (8^45, 10^36).
This script checks every missing edge and proves that adding even one creates
a C4.  Hence no edge-addition repair can raise its minimum degree to 9.

This is a construction-class result only, not global q=9 nonexistence.
"""

from __future__ import annotations

import itertools
import json

from er9_induced81_search import polarity_graph


def c4_free(adjacency: list[set[int]]) -> bool:
    return all(
        len(adjacency[u] & adjacency[v]) <= 1
        for u in range(len(adjacency))
        for v in range(u + 1, len(adjacency))
    )


def edge_is_safe(adjacency: list[set[int]], u: int, v: int) -> bool:
    """An added edge uv is safe iff no existing length-three u-v path."""
    assert u != v and v not in adjacency[u]
    return not any(
        adjacency[middle] & adjacency[v]
        for middle in adjacency[u]
    )


def main() -> None:
    _, er9_adjacency = polarity_graph()
    absolute = {
        vertex for vertex, neighbors in enumerate(er9_adjacency)
        if len(neighbors) == 9
    }
    assert len(absolute) == 10
    retained = [v for v in range(91) if v not in absolute]
    relabel = {vertex: index for index, vertex in enumerate(retained)}
    adjacency = [
        {relabel[w] for w in er9_adjacency[v] if w in relabel}
        for v in retained
    ]
    assert len(adjacency) == 81
    assert c4_free(adjacency)
    degree_histogram = {
        degree: sum(len(neighbors) == degree for neighbors in adjacency)
        for degree in {len(neighbors) for neighbors in adjacency}
    }
    assert degree_histogram == {8: 45, 10: 36}

    missing_edges = [
        (u, v) for u, v in itertools.combinations(range(81), 2)
        if v not in adjacency[u]
    ]
    safe_edges = [
        (u, v) for u, v in missing_edges
        if edge_is_safe(adjacency, u, v)
    ]
    # Cross-check the length-three-path criterion directly for any alleged
    # safe edge.  In the actual q=9 result the list is empty.
    for u, v in safe_edges:
        repaired = [neighbors.copy() for neighbors in adjacency]
        repaired[u].add(v)
        repaired[v].add(u)
        assert c4_free(repaired)
    assert not safe_edges

    print(json.dumps({
        "retained_vertices": len(adjacency),
        "degree_histogram": degree_histogram,
        "missing_edges_checked": len(missing_edges),
        "individually_safe_added_edges": len(safe_edges),
        "result": "EDGE-MAXIMAL-C4-FREE",
        "scope": "ER_9 with all ten absolute points deleted",
    }, sort_keys=True))


if __name__ == "__main__":
    main()
