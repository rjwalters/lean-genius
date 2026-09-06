#!/usr/bin/env python3
"""Verify separate C4-free star completions of every exterior Euler-core label.

Only Python's standard library is needed. These stars must NOT be superimposed.
"""

import json
from itertools import combinations
from pathlib import Path

from check_size_two_euler_partial_graph import TOUR


def check(model):
    assert model["q"] == 16
    q, size = 16, 32
    defects = (set(range(1, size, 2)) - {1, size - 1}) | {q}
    steps = set(range(1, size)) - defects - {2, size - 2}
    selectors = [edge for edge in combinations(range(size), 2)
                 if edge[1] - edge[0] in steps]
    labels = {edge: size + i for i, edge in enumerate(selectors)}
    assert len(labels) == 224
    base = [set() for _ in range(q * q)]

    def add(graph, a, b):
        assert a != b
        graph[a].add(b)
        graph[b].add(a)

    for a in range(size):
        add(base, a, (a + 1) % size)
    for edge, f in labels.items():
        for a in edge:
            add(base, a, f)
    for parity in (0, 1):
        cycle = [labels[tuple(sorted((2 * TOUR[i] + parity,
                                     2 * TOUR[(i + 1) % len(TOUR)] + parity)))]
                 for i in range(len(TOUR))]
        assert len(cycle) == len(set(cycle)) == 96
        for a, b in zip(cycle, cycle[1:] + cycle[:1]):
            add(base, a, b)

    pairs = list(combinations(range(q * q), 2))
    assert all(len(base[a] & base[b]) <= 1 for a, b in pairs)
    seen = set()
    new_edge_count = 0
    for star in model["stars"]:
        edge = tuple(star["selector"])
        e = labels[edge]
        assert e not in seen
        seen.add(e)
        additions = [labels[tuple(other)] for other in star["new_neighbors"]]
        assert len(additions) == len(set(additions)) == q - len(base[e])
        graph = [neighbors.copy() for neighbors in base]
        for f in additions:
            assert f != e and f not in base[e]
            add(graph, e, f)
        assert len(graph[e]) == q
        assert all(len(graph[a]) == q for a in range(size))
        assert all(len(neighbors) <= q for neighbors in graph)
        # Independent full-graph check, not the discovery solver's local cuts.
        assert all(len(graph[a] & graph[b]) <= 1 for a, b in pairs)
        exterior_neighbors = graph[e] - set(range(size))
        covered = [a for f in exterior_neighbors for a in selectors[f - size]]
        holes = {(a + step) % size for a in edge for step in (-1, 1)}
        assert len(covered) == len(set(covered)) == 2 * (q - 2)
        assert set(covered) == set(range(size)) - holes
        # Only e has been fully completed among F; the rest remain low-degree.
        assert sum(len(graph[f]) == q for f in range(size, q * q)) == 1
        new_edge_count += len(additions)
    assert seen == set(labels.values())
    assert new_edge_count == 2752
    return dict(q=q, separately_completed_vertices=len(seen),
                checked_vertex_pairs=len(seen) * len(pairs),
                every_completed_graph_c4_free=True,
                common_regular_completion=False)


if __name__ == "__main__":
    path = Path(__file__).with_name("size_two_euler_star_completions_q16.json")
    print(check(json.loads(path.read_text())))
