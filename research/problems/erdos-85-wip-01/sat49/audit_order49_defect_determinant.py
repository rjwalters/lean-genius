#!/usr/bin/env python3
"""Audit the strengthened order-49 defect determinant obstruction.

This is a bounded falsification probe, not a graph-completion search.  It
samples connected simple graphs with the ordinary-defect degree profile
``3 x 4, 18 x 5, 25 x 6`` and computes

    T = 10 det(L) + 7 1^T adj(L) 1,       L = 6 I - A(D).

The three-high spectral factor forces an actual realization to satisfy
``T = 49 q^2``.  Random profile graphs test whether divisibility by 49, and
then the square quotient, are selective enough to merit a structural proof.
"""

from __future__ import annotations

import argparse
import math
import random
from collections import Counter

import networkx as nx

from audit_h16_circulant_tree_squares import bareiss_determinant


DEGREES = [4] * 3 + [5] * 18 + [6] * 25


def defect_matrices(graph: nx.Graph) -> tuple[list[list[int]], list[list[int]]]:
    n = len(DEGREES)
    lap = [
        [6 if i == j else -int(graph.has_edge(i, j)) for j in range(n)]
        for i in range(n)
    ]
    bordered = [row + [1] for row in lap]
    bordered.append([1] * n + [0])
    return lap, bordered


def determinant_expression(graph: nx.Graph) -> int:
    lap, bordered = defect_matrices(graph)
    det_lap = bareiss_determinant(lap)
    # det [[L,1],[1^T,0]] = -1^T adj(L) 1.
    forest_bordered = -bareiss_determinant(bordered)
    return 10 * det_lap + 7 * forest_bordered


def randomized_profile_graph(rng: random.Random, swaps: int) -> nx.Graph:
    graph = nx.havel_hakimi_graph(DEGREES)
    # NetworkX accepts an explicit Random instance and preserves the degrees.
    nx.double_edge_swap(graph, nswap=swaps, max_tries=100 * swaps, seed=rng)
    return graph


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--samples", type=int, default=100)
    parser.add_argument("--swaps", type=int, default=500)
    parser.add_argument("--seed", type=int, default=850049)
    args = parser.parse_args()

    rng = random.Random(args.seed)
    residues: Counter[int] = Counter()
    connected = divisible = square_quotient = 0
    for _ in range(args.samples):
        graph = randomized_profile_graph(rng, args.swaps)
        if not nx.is_connected(graph):
            continue
        connected += 1
        value = determinant_expression(graph)
        residues[value % 49] += 1
        if value % 49:
            continue
        divisible += 1
        quotient = value // 49
        if quotient >= 0 and math.isqrt(quotient) ** 2 == quotient:
            square_quotient += 1

    print("samples", args.samples, "connected", connected)
    print("divisible_by_49", divisible, "forty_nine_times_square", square_quotient)
    print("residues_mod_49", dict(sorted(residues.items())))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
