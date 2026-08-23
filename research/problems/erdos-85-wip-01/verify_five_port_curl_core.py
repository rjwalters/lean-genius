#!/usr/bin/env python3
"""Verify the minimal five-port simultaneous-curl incidence core."""

from itertools import combinations


def edge(a: str, b: str) -> tuple[str, str]:
    return tuple(sorted((a, b)))


ports = [f"p{i}" for i in range(5)]
roots = [f"x{i}" for i in range(5)]
labels = [f"y{i}" for i in range(5)]
vertices = ports + roots + labels
edges: set[tuple[str, str]] = set()

for i in range(5):
    # p_i indexes the marked H edge x_i--x_(i+1).
    edges.add(edge(ports[i], roots[i]))
    edges.add(edge(ports[i], roots[(i + 1) % 5]))
    edges.add(edge(roots[i], roots[(i + 1) % 5]))

    # The complementary port C5 has edges p_i--p_(i+2), indexed by y_i.
    edges.add(edge(labels[i], ports[i]))
    edges.add(edge(labels[i], ports[(i + 2) % 5]))

adjacency = {v: set() for v in vertices}
for a, b in edges:
    adjacency[a].add(b)
    adjacency[b].add(a)

codegrees = {
    (a, b): len(adjacency[a] & adjacency[b])
    for a, b in combinations(vertices, 2)
}

assert len(vertices) == 15
assert len(edges) == 25
assert {len(adjacency[p]) for p in ports} == {4}
assert {len(adjacency[x]) for x in roots} == {4}
assert {len(adjacency[y]) for y in labels} == {2}
assert max(codegrees.values()) == 1

print("five-port curl core: 15 vertices, 25 edges, maximum codegree 1")
