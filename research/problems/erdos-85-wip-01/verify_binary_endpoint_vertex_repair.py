#!/usr/bin/env python3
"""Finite calibration of the companion uniform vertex-repair obstruction."""

from collections import Counter
from itertools import combinations

from verify_binary_post_square_interval import polarity_graph


def check(q, modulus):
    adjacency, absolute, nucleus = polarity_graph(q, modulus)
    vertices = set(range(len(adjacency)))
    looped = [neighbors | ({v} if v in absolute else set())
              for v, neighbors in enumerate(adjacency)]
    assert all(len(row) == q + 1 for row in looped)
    assert all(len(looped[x] & looped[y]) == 1
               for x, y in combinations(vertices, 2))
    a = min(absolute)
    retained = vertices - ({a} | (adjacency[a] - {nucleus}))
    h = {v: adjacency[v] & retained for v in retained}
    assert len(h) == q*q + 1
    assert all(len(h[v]) == q and len(looped[v] - h[v]) == 1
               for v in retained)
    assert all(len(h[x] & h[y]) <= 1
               for x, y in combinations(retained, 2))
    histogram = Counter()
    for v in sorted(retained):
        for x, y in combinations(sorted(h[v]), 2):
            if y in h[x]:
                continue
            # Enumerate ordered internal vertices directly, with all four
            # path vertices distinct, rather than relying on matrix powers.
            paths = [(u, w) for u in h[x] - {v}
                     for w in h[y] - {v}
                     if w in h[u] and len({x, u, w, y}) == 4]
            assert len(paths) >= q - 3
            assert paths, (q, v, x, y)
            histogram[len(paths)] += 1
            u, w = paths[0]
            repaired = {z: h[z] - {v} for z in retained - {v}}
            repaired[x].add(y)
            repaired[y].add(x)
            # x-u-w-y-x is an actual C4 in this proposed repaired graph.
            assert u in repaired[x] and w in repaired[u]
            assert y in repaired[w] and x in repaired[y]
    assert histogram
    print(f"q={q}: all {len(retained)} deletions checked; "
          f"candidate-edge path counts {dict(sorted(histogram.items()))}; "
          "no safe edge PASS")


if __name__ == "__main__":
    for parameters in [(2, 0b111), (4, 0b111), (8, 0b1011), (16, 0b10011)]:
        check(*parameters)
