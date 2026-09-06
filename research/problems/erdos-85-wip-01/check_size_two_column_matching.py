#!/usr/bin/env python3
"""Finite sanity checks of the uniform column-matching proof, not a census.

Requires networkx. No symmetric exterior graph or ambient witness is produced.
"""

import argparse
from collections import Counter

import networkx as nx


def check(q: int) -> None:
    assert q >= 12 and q % 2 == 0
    vertices = set(range(2 * q))
    forbidden = {d for d in range(1, 2 * q)
                 if (d % 2 and d not in (1, 2 * q - 1)) or d == q}
    forbidden.update((2, 2 * q - 2))
    graph = nx.Graph()
    graph.add_nodes_from(vertices)
    graph.add_edges_from((a, b) for a in vertices for b in vertices
                         if a < b and (b - a) % (2 * q) not in forbidden)
    assert all(graph.degree(v) == q - 2 for v in vertices)
    columns = {}
    used_rows = Counter()
    for a, b in graph.edges:
        edge = tuple(sorted((a, b)))
        holes = {(v + d) % (2 * q) for v in edge for d in (-1, 1)}
        assert len(holes) == 4
        selected = set()
        for parity in (0, 1):
            support = {v for v in vertices - holes if v % 2 == parity}
            block = graph.subgraph(support).copy()
            if block.has_edge(a, b):
                block.remove_edge(a, b)
            assert len(block) % 2 == 0
            assert min(dict(block.degree()).values()) >= len(block) // 2
            matching = nx.max_weight_matching(block, maxcardinality=True)
            assert 2 * len(matching) == len(block)
            selected.update(tuple(sorted(pair)) for pair in matching)
        incidence = Counter(v for pair in selected for v in pair)
        # Checks the actual column of BT=J-HB, not only its sum.
        assert all(incidence[v] == int(v not in holes) for v in vertices)
        assert len(selected) == q - 2 and edge not in selected
        assert all(graph.has_edge(*pair) for pair in selected)
        assert all(a % 2 == b % 2 for a, b in selected)
        columns[edge] = selected
        used_rows.update(selected)
    cross_edge = (0, 1)
    assert cross_edge in columns and len(columns[cross_edge]) == q - 2
    assert used_rows[cross_edge] == 0
    neighbor = next(iter(columns[cross_edge]))
    assert cross_edge not in columns[neighbor]  # Explicit symmetry failure.
    print(f"q={q}: {len(columns)} loopless columns verified; symmetry absent")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("q", nargs="*", type=int, default=[12, 14, 16, 32])
    args = parser.parse_args()
    for order in args.q:
        check(order)
