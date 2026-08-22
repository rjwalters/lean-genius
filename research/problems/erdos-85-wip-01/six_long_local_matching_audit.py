#!/usr/bin/env python3
"""Local Hall audit for the classified C6 + C_(2q-6) trace graphs."""

from argparse import ArgumentParser
from itertools import combinations

import networkx as nx


def cycle_edges(vertices):
    return {tuple(sorted((vertices[i], vertices[(i + 1) % len(vertices)])))
            for i in range(len(vertices))}


def trace_graph(q: int, step: int):
    n = q - 3
    short = tuple(range(6))
    long = tuple(range(6, 6 + 2 * n))
    h_edges = cycle_edges(short) | cycle_edges(long)
    f_edges = {tuple(sorted((i, (i + 3) % 6))) for i in range(3)}
    for i, j in combinations(range(2 * n), 2):
        if (i - j) % 2 and (j - i) % (2 * n) not in {step, -step % (2 * n)}:
            f_edges.add(tuple(sorted((6 + i, 6 + j))))
    for i in short:
        for j in range(2 * n):
            if (i - j) % 2:
                f_edges.add(tuple(sorted((i, 6 + j))))
    return tuple(range(2 * q)), h_edges, f_edges


def audit(q: int, step: int):
    vertices, h_edges, f_edges = trace_graph(q, step)
    h_neighbors = {v: set() for v in vertices}
    for u, v in h_edges:
        h_neighbors[u].add(v)
        h_neighbors[v].add(u)
    graph = nx.Graph()
    graph.add_nodes_from(vertices)
    graph.add_edges_from(f_edges)
    for trace in f_edges:
        eligible = set(vertices) - h_neighbors[trace[0]] - h_neighbors[trace[1]]
        matching = nx.algorithms.matching.max_weight_matching(graph.subgraph(eligible), maxcardinality=True)
        if 2 * len(matching) != len(eligible):
            return False, trace, len(eligible), 2 * len(matching)
    return True, None, None, None


if __name__ == "__main__":
    parser = ArgumentParser()
    parser.add_argument("q", type=int, nargs="+")
    args = parser.parse_args()
    for q in args.q:
        n2 = 2 * (q - 3)
        for step in range(3, n2 // 2 + 1, 2):
            result = audit(q, step)
            print(f"q={q} step={step}: {'PASS' if result[0] else result}")
