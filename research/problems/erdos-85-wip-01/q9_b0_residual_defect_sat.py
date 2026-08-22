#!/usr/bin/env python3
"""Residual B0 defect-coupling probe for the q=9 second profile.

The 47 ordinary B0 vertices split into 26 U1-triple centers and three
seven-point marked-support sets.  The support holes are exactly the 2/4
exceptional D(x)-neighbors.  For a vertex t, counting its common neighbors
with the 24 unmarked B1 vertices gives

  common(t,U1) = 3 * u1_degree(t) + sum_{s~t} u1_degree(s).

Combining this with the exact B0--B1 defect type says that the number of
marked B1 defect neighbors is determined by t's number of triple-center
neighbors.  A marked point m is defect-adjacent to t exactly when t has no
residual neighbor in m's seven-point support.  This script tests that exact
47-vertex coupling, with the C4-free common-neighbor bound and the known
special-support incidence intersections.

Exploratory only: a SAT result is a failure certificate for this abstraction;
an UNSAT result still needs a checked proof or independently verified CNF.
"""

from __future__ import annotations

import argparse
import time
from itertools import combinations

from z3 import And, Bool, If, SolverFor, Sum, sat, unknown


N_TRIPLE = 26
N_PAIR = 21
N = N_TRIPLE + N_PAIR


def edge_key(u: int, v: int) -> tuple[int, int]:
    assert u != v
    return (u, v) if u < v else (v, u)


N_U1 = 24


def color(v: int) -> int:
    return v // 8


def build(branch: int, timeout_ms: int, full_incidence: bool) -> tuple[Solver, dict]:
    if branch not in (3, 4):
        raise ValueError("branch must be 3 or 4")
    holes = 2 if branch == 3 else 4
    classes = N_TRIPLE - holes
    solver = SolverFor("QF_FD")
    solver.set(timeout=timeout_ms)
    edges = {edge_key(u, v): Bool(f"r_{u}_{v}") for u, v in combinations(range(N), 2)}

    def adj(u: int, v: int):
        return False if u == v else edges[edge_key(u, v)]

    # Canonicalize the anonymous triple centers: class centers first, holes last.
    is_hole = lambda u: classes <= u < N_TRIPLE
    pair_groups = [range(N_TRIPLE + 7 * g, N_TRIPLE + 7 * (g + 1)) for g in range(3)]

    miss = {}
    for u in range(N):
        degree = Sum([If(adj(u, v), 1, 0) for v in range(N) if v != u])
        solver.add(degree == (6 if is_hole(u) or u >= N_TRIPLE else 5))
        triple_neighbors = Sum([If(adj(u, v), 1, 0) for v in range(N_TRIPLE) if v != u])
        for g, support in enumerate(pair_groups):
            miss[u, g] = Bool(f"miss_{u}_{g}")
            solver.add(miss[u, g] == (Sum([If(adj(u, v), 1, 0) for v in support]) == 0))
        marked_defect = Sum([If(miss[u, g], 1, 0) for g in range(3)])
        if is_hole(u):
            # Exceptional type has no B1 defect neighbors; common(t,U1)=24.
            solver.add(triple_neighbors == 3)
            solver.add(marked_defect == 0)
        elif u < N_TRIPLE:
            # Regular triple center: d_M = n_triple - 2.
            solver.add(marked_defect == triple_neighbors - 2)
        else:
            # Regular pair center: d_M = n_triple - 3.
            solver.add(marked_defect == triple_neighbors - 3)

    # Each marked B1 vertex has exactly five B0 defect neighbors.
    for g in range(3):
        solver.add(Sum([If(miss[u, g], 1, 0) for u in range(N)]) == 5)

    # Residual C4-freeness: two B0 vertices have at most one common residual
    # neighbor.  If their U1 incidence blocks intersect, that already supplies
    # a common neighbor, so they may have none in the residual graph.  The
    # detailed block intersections are optional input to a later refinement;
    # the unconditional at-most-one constraint is already necessary.
    for u, v in combinations(range(N), 2):
        common = [If(adj(u, w) & adj(v, w), 1, 0) for w in range(N) if w not in (u, v)]
        solver.add(Sum(common) <= 1)

    incidence = {}
    k = {}
    defect_u1 = {}
    if full_incidence:
        # Original B0--U1 incidence.  Triple centers are rainbow triples;
        # pair center group g avoids color g.  Every U1 point has degree five.
        incidence = {(u, b): Bool(f"i_{u}_{b}") for u in range(N) for b in range(N_U1)}
        for u in range(N):
            if u < N_TRIPLE:
                for c in range(3):
                    solver.add(Sum([If(incidence[u, b], 1, 0) for b in range(N_U1) if color(b) == c]) == 1)
            else:
                g = (u - N_TRIPLE) // 7
                for c in range(3):
                    target = 0 if c == g else 1
                    solver.add(Sum([If(incidence[u, b], 1, 0) for b in range(N_U1) if color(b) == c]) == target)
        for b in range(N_U1):
            solver.add(Sum([If(incidence[u, b], 1, 0) for u in range(N)]) == 5)

        # Special-support parallel classes and marked-support matchings.
        if branch == 3:
            class_ranges = [range(0, 8), range(8, 16), range(16, 24)]
        else:
            class_ranges = [range(0, 8), range(8, 15), range(15, 22)]
        for r, centers in enumerate(class_ranges):
            for b in range(N_U1):
                hits = Sum([If(incidence[u, b], 1, 0) for u in centers])
                solver.add(hits == 1 if r == 0 or branch == 3 else hits <= 1)
        for g, centers in enumerate(pair_groups):
            for b in range(N_U1):
                solver.add(Sum([If(incidence[u, b], 1, 0) for u in centers]) <= 1)

        # Two B0 centers cannot have two common U1 points; an existing U1
        # common point also consumes their residual common-neighbor allowance.
        for u, v in combinations(range(N), 2):
            block_common = Sum([If(And(incidence[u, b], incidence[v, b]), 1, 0) for b in range(N_U1)])
            residual_common = Sum([If(adj(u, w) & adj(v, w), 1, 0) for w in range(N) if w not in (u, v)])
            solver.add(block_common + residual_common <= 1)

        # Cubic U1 graph: one neighbor of every high color at every point.
        k = {edge_key(a, b): Bool(f"k_{a}_{b}") for a, b in combinations(range(N_U1), 2)}

        def kadj(a: int, b: int):
            return False if a == b else k[edge_key(a, b)]

        for a in range(N_U1):
            for c in range(3):
                solver.add(Sum([If(kadj(a, b), 1, 0) for b in range(N_U1) if b != a and color(b) == c]) == 1)

        # Exact zero-slack pair cover on U1, now using the 47 actual B0 blocks.
        for a, b in combinations(range(N_U1), 2):
            common_k = [And(kadj(a, c), kadj(b, c)) for c in range(N_U1) if c not in (a, b)]
            common_b0 = [And(incidence[u, a], incidence[u, b]) for u in range(N)]
            if color(a) == color(b):
                solver.add(Sum([If(q, 1, 0) for q in common_k + common_b0]) == 0)
            else:
                defect_u1[edge_key(a, b)] = Bool(f"du_{a}_{b}")
                solver.add(Sum([If(q, 1, 0) for q in common_k + common_b0 + [defect_u1[edge_key(a, b)]]]) == 1)

        # Full B0--B1 defect coupling.  D(t,b) iff t,b have no common
        # original neighbor.  Row degrees are 3 for regular B0 and 0 for the
        # exceptional hole centers; each U1 column has total B0 defect degree
        # five after adding the two branch-4 special antipodal fibers.
        dtb = {(u, b): Bool(f"dtb_{u}_{b}") for u in range(N) for b in range(N_U1)}
        for u in range(N):
            for b in range(N_U1):
                common = (
                    [And(incidence[u, c], kadj(c, b)) for c in range(N_U1) if c != b]
                    + [And(adj(u, v), incidence[v, b]) for v in range(N) if v != u]
                )
                common_count = Sum([If(q, 1, 0) for q in common])
                solver.add(common_count <= 1)
                solver.add(dtb[u, b] == (common_count == 0))
            target = 0 if is_hole(u) else 3
            solver.add(Sum([If(dtb[u, b], 1, 0) for b in range(N_U1)]) + Sum([If(miss[u, g], 1, 0) for g in range(3)]) == target)
        for b in range(N_U1):
            special = 0
            if branch == 4:
                # Missing a punctured class is exactly antipodality to its
                # regular special endpoint.
                special = Sum([
                    If(Sum([If(incidence[u, b], 1, 0) for u in class_ranges[r]]) == 0, 1, 0)
                    for r in (1, 2)
                ])
            solver.add(Sum([If(dtb[u, b], 1, 0) for u in range(N)]) + special == 5)

    return solver, {"edges": edges, "miss": miss, "classes": classes,
                    "incidence": incidence, "k": k, "defect_u1": defect_u1}


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--branch", type=int, choices=(3, 4), required=True)
    parser.add_argument("--timeout-seconds", type=int, default=300)
    parser.add_argument("--full-incidence", action="store_true")
    args = parser.parse_args()
    solver, data = build(args.branch, args.timeout_seconds * 1000, args.full_incidence)
    started = time.time()
    result = solver.check()
    elapsed = time.time() - started
    print(f"branch={args.branch} result={result} elapsed={elapsed:.3f}s")
    if result == sat:
        model = solver.model()
        chosen = [e for e, var in data["edges"].items() if bool(model.eval(var, model_completion=True))]
        print(f"residual_edges={len(chosen)}")
        print("marked_defect_hist=" + str([
            sum(bool(model.eval(data["miss"][u, g], model_completion=True)) for u in range(N))
            for g in range(3)
        ]))
    elif result == unknown:
        print(f"reason_unknown={solver.reason_unknown()}")
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
