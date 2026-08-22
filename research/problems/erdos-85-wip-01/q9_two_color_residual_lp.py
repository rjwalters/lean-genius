#!/usr/bin/env python3
"""LP probe for the q=9 two-color residual-fiber obstruction.

For a fixed outer Q,K witness, retain only three necessary conditions on the
47-row residual adjacency A:

* the proved row degrees (5 on regular triple rows, 6 otherwise);
* both trace-zero support directions on every possible A-edge;
* |N_A(t) intersect F_b| <= 1 for the sixteen U1 fibers in two colors.

The variables are relaxed to [0,1].  LP infeasibility is therefore a failure
certificate for this abstraction and evidence for a weighted counting proof;
it is not a universal certificate for all outer designs.
"""

from __future__ import annotations

import argparse
import sys
from itertools import combinations

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import lil_matrix

from q9_b0_residual_defect_sat import (
    N,
    N_TRIPLE,
    N_U1,
    make_outer_seed,
)


def solve(branch: int, seed: dict, colors: tuple[int, int]) -> tuple[int, int, str]:
    blocks = [set(block) for block in seed["blocks"]]
    k_neighbors = [set() for _ in range(N_U1)]
    for a, b in seed["k_edges"]:
        k_neighbors[a].add(b)
        k_neighbors[b].add(a)
    core_support = [
        set().union(*(k_neighbors[b] for b in block)) for block in blocks
    ]
    fibers = [[u for u in range(N) if b in blocks[u]] for b in range(N_U1)]

    # An edge is allowed only when both residual/core trace-zero directions
    # hold.  All other adjacency variables are fixed to zero and omitted.
    edges = [
        (u, v) for u, v in combinations(range(N), 2)
        if not (blocks[v] & core_support[u])
        and not (blocks[u] & core_support[v])
    ]
    edge_index = {edge: i for i, edge in enumerate(edges)}

    degree_eq = lil_matrix((N, len(edges)))
    for j, (u, v) in enumerate(edges):
        degree_eq[u, j] = 1
        degree_eq[v, j] = 1
    holes = 2 if branch == 3 else 4
    regular_triples = N_TRIPLE - holes
    degree_rhs = np.array([
        5 if u < regular_triples else 6 for u in range(N)
    ])

    selected = [
        b for color in colors for b in range(8 * color, 8 * color + 8)
    ]
    cap_rows = [(t, b) for t in range(N) for b in selected]
    caps = lil_matrix((len(cap_rows), len(edges)))
    for i, (t, b) in enumerate(cap_rows):
        for u in fibers[b]:
            if u == t:
                continue
            edge = (t, u) if t < u else (u, t)
            if edge in edge_index:
                caps[i, edge_index[edge]] = 1

    result = linprog(
        np.zeros(len(edges)),
        A_ub=caps.tocsr(),
        b_ub=np.ones(len(cap_rows)),
        A_eq=degree_eq.tocsr(),
        b_eq=degree_rhs,
        bounds=(0, 1),
        method="highs",
    )
    status = "feasible" if result.success else "infeasible"
    if result.status not in (0, 2):
        status = f"unknown(status={result.status})"
    return len(edges), len(cap_rows), status


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--seeds", type=int, default=4)
    parser.add_argument("--timeout-seconds", type=int, default=300)
    args = parser.parse_args()
    if args.seeds <= 0:
        parser.error("--seeds must be positive")
    for branch in (3, 4):
        for seed_number in range(args.seeds):
            seed = make_outer_seed(
                branch, args.timeout_seconds * 1000, seed_number
            )
            for colors in combinations(range(3), 2):
                edge_count, cap_count, status = solve(
                    branch, seed, colors,
                )
                print(
                    f"branch={branch} seed={seed_number} colors={colors} "
                    f"allowed_edges={edge_count} caps={cap_count} lp={status}"
                )
    return 0


if __name__ == "__main__":
    sys.exit(main())
