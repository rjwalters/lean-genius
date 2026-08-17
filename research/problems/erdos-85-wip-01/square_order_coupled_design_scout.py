#!/usr/bin/env python3
"""Scout the coupled high-block/defect constraints for q=8 profiles.

This is a discovery model, not a proof certificate.  It realizes every low
vertex individually, simultaneously imposing the proved high-incidence block
design, defect degree/weight equations, and the owner-sensitive common-defect
bound.  UNSAT is therefore useful evidence for a new structural target; SAT
only means this relaxation survives.
"""

import argparse
from pathlib import Path
import time

import z3

from square_order_branch_profile_census import arithmetic_profiles, vertex_type_feasible
from square_order_combined_profile_census import defect_weight_class_feasible


def surviving_profiles():
    return [
        (h, counts)
        for h, counts in arithmetic_profiles()
        if all(
            vertex_type_feasible(h, counts, k)
            for k, multiplicity in enumerate(counts)
            if multiplicity
        )
        and defect_weight_class_feasible(h, counts)
    ]


def coupled_solver(
    h, counts, timeout_ms, coupling=True, omit_block=False, omit_defect=False,
    full_graph=False, h2_split=None,
):
    weights = [k for k, count in enumerate(counts) for _ in range(count)]
    n = len(weights)
    solver = z3.Solver()
    solver.set(timeout=timeout_ms)

    block = [[z3.Bool(f"b_{u}_{a}") for a in range(h)] for u in range(n)]
    defect = [[None for _ in range(n)] for _ in range(n)]
    low_adj = [[None for _ in range(n)] for _ in range(n)]
    for u in range(n):
        defect[u][u] = z3.BoolVal(False)
        low_adj[u][u] = z3.BoolVal(False)
        for v in range(u + 1, n):
            edge = z3.Bool(f"d_{u}_{v}")
            defect[u][v] = defect[v][u] = edge
            gedge = z3.Bool(f"g_{u}_{v}")
            low_adj[u][v] = low_adj[v][u] = gedge

    # Low/high incidence is a packing with low block size k(u).  A high vertex
    # has total G-degree 9, but some of those neighbors may themselves be high,
    # so its low-column degree is only bounded above by 9.  A high pair occurs
    # at most once among low blocks.
    h2_profile = h == 2 and tuple(counts) == (45, 16, 1, 0, 0)
    if not omit_block:
        for u, k in enumerate(weights):
            solver.add(z3.PbEq([(x, 1) for x in block[u]], k))
        for a in range(h):
            solver.add(z3.PbLe([(block[u][a], 1) for u in range(n)], 9))
        for a in range(h):
            for b in range(a + 1, h):
                solver.add(
                    z3.PbLe([(z3.And(block[u][a], block[u][b]), 1) for u in range(n)], 1)
                )

    # Break high-label symmetry and equal-weight low-row symmetry.
    first_positive = next((u for u, k in enumerate(weights) if k), None)
    if first_positive is not None and not omit_block and not h2_profile:
        k = weights[first_positive]
        for a in range(h):
            solver.add(block[first_positive][a] == (a < k))
    row_codes = [z3.Sum([z3.If(block[u][a], 1 << a, 0) for a in range(h)]) for u in range(n)]
    if not omit_block and not h2_profile:
        for u in range(n - 1):
            if weights[u] == weights[u + 1]:
                solver.add(row_codes[u] <= row_codes[u + 1])

    # Defect equations: deg_D(u)=7-k(u), and (D+I)k=h1.
    if not omit_defect:
        for u, k in enumerate(weights):
            solver.add(z3.PbEq([(defect[u][v], 1) for v in range(n) if v != u], 7 - k))
            solver.add(
                z3.PbEq(
                    [(defect[u][v], weights[v]) for v in range(n) if v != u],
                    h - k,
                )
            )

    # Every low pair has at most one common high.  A D-edge has none.  For a
    # D-nonedge the proved owner-sensitive grid inequality is
    #   commonD + k(u)+k(v) <= 7 + commonHigh.
    if omit_block or omit_defect:
        return solver
    if full_graph:
        # Incidence totals equal 9h, so the column upper bounds above are all
        # tight and the high sector is independent.  Complete G by its
        # low-low adjacency matrix and impose every remaining C4 constraint.
        for u, k in enumerate(weights):
            solver.add(
                z3.PbEq([(low_adj[u][v], 1) for v in range(n) if v != u], 8 - k)
            )
        if h2_profile:
            # The k=1 rows are sorted as eight {0}'s followed by eight {1}'s.
            # Their D-neighbor weight equation makes D on these 16 vertices a
            # cross-class perfect matching, canonical up to the two S_8 label
            # actions.  The unique k=2 vertex has five interchangeable k=0
            # D-neighbors.
            for u in range(62):
                expected = (
                    (False, False) if u < 45 else
                    (True, False) if u < 53 else
                    (False, True) if u < 61 else
                    (True, True)
                )
                for a in range(2):
                    solver.add(block[u][a] == expected[a])
            left = range(45, 53)
            right = range(53, 61)
            for i, u in enumerate(left):
                for j, v in enumerate(right):
                    solver.add(defect[u][v] == (i == j))
            for u in range(45):
                solver.add(defect[61][u] == (u < 5))
            if h2_split is not None:
                left_count, right_count, t_count = h2_split
                if left_count not in (0, 1) or right_count not in (0, 1):
                    raise ValueError("h=2 high-class neighborhood counts must be 0 or 1")
                u_count = 6 - left_count - right_count - t_count
                if not 0 <= t_count <= 5 or not 0 <= u_count <= 40:
                    raise ValueError("invalid h=2 neighborhood split")
                # N_G(x) has maximum degree one internally.  Hence it contains
                # at most one point from each high singleton class; the two
                # selected singleton points cannot be a matched D-pair.
                selected = (
                    set(range(45, 45 + left_count))
                    | set(range(53 + left_count, 53 + left_count + right_count))
                    | set(range(0, t_count))
                    | set(range(5, 5 + u_count))
                )
                for u in range(61):
                    solver.add(low_adj[61][u] == (u in selected))
                if left_count == right_count == 1 and u_count % 2 == 0:
                    # The selected U vertices have their unique S-neighbor
                    # inside U∩S, hence form a matching; fix that matching.
                    selected_u = list(range(5, 5 + u_count))
                    for i, u in enumerate(selected_u):
                        for j, v in enumerate(selected_u):
                            if i < j:
                                solver.add(low_adj[u][v] == (j == (i ^ 1)))
                    # Every U vertex has exactly one S-neighbor.  Canonically
                    # partition the external U vertices among the six rows;
                    # k=1 rows need six, selected T rows seven, and selected U
                    # rows six externally (plus their matched S-partner).
                    s_rows = [45, 54] + list(range(t_count)) + selected_u
                    quotas = [6, 6] + [7] * t_count + [6] * u_count
                    external_u = list(range(5 + u_count, 45))
                    owner = {}
                    cursor = 0
                    for s, quota in zip(s_rows, quotas):
                        for z in external_u[cursor : cursor + quota]:
                            owner[z] = s
                        cursor += quota
                    assert cursor == len(external_u)
                    for s in s_rows:
                        for z in selected_u:
                            expected_internal = (
                                s in selected_u
                                and selected_u.index(z) == (selected_u.index(s) ^ 1)
                            )
                            solver.add(low_adj[s][z] == expected_internal)
                        for z in external_u:
                            solver.add(low_adj[s][z] == (owner[z] == s))
        for u in range(n):
            for v in range(u + 1, n):
                common = [
                    z3.And(low_adj[u][w], low_adj[v][w])
                    for w in range(n)
                    if w != u and w != v
                ] + [z3.And(block[u][a], block[v][a]) for a in range(h)]
                solver.add(z3.PbLe([(x, 1) for x in common], 1))
                solver.add(z3.Implies(defect[u][v], z3.PbEq([(x, 1) for x in common], 0)))
                solver.add(z3.Implies(z3.Not(defect[u][v]), z3.PbEq([(x, 1) for x in common], 1)))
        for u in range(n):
            for a in range(h):
                common = [
                    z3.And(low_adj[u][v], block[v][a])
                    for v in range(n)
                    if v != u
                ]
                solver.add(z3.PbLe([(x, 1) for x in common], 1))
        return solver
    for u in range(n):
        for v in range(u + 1, n):
            common_high = z3.Sum(
                [z3.If(z3.And(block[u][a], block[v][a]), 1, 0) for a in range(h)]
            )
            solver.add(common_high <= 1)
            if not coupling:
                continue
            solver.add(z3.Implies(defect[u][v], common_high == 0))
            common_defect = z3.Sum(
                [
                    z3.If(z3.And(defect[u][w], defect[v][w]), 1, 0)
                    for w in range(n)
                    if w != u and w != v
                ]
            )
            solver.add(
                z3.Implies(
                    z3.Not(defect[u][v]),
                    common_defect + weights[u] + weights[v] <= 7 + common_high,
                )
            )
    return solver


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--index", type=int, help="run only this survivor index")
    parser.add_argument("--h", type=int, help="run only profiles with this h")
    parser.add_argument("--timeout", type=float, default=20.0, help="seconds per profile")
    parser.add_argument("--no-coupling", action="store_true", help="omit all G/D pair coupling")
    parser.add_argument("--block-only", action="store_true")
    parser.add_argument("--defect-only", action="store_true")
    parser.add_argument("--full-graph", action="store_true", help="reconstruct exact G")
    parser.add_argument(
        "--h2-split",
        nargs=3,
        type=int,
        metavar=("LEFT", "RIGHT", "T"),
        help="canonical split of the unique k=2 vertex's six low G-neighbors",
    )
    parser.add_argument(
        "--write-dimacs",
        type=Path,
        help="lower one selected pure-Boolean model to DIMACS instead of solving",
    )
    args = parser.parse_args()

    profiles = surviving_profiles()
    selected = list(enumerate(profiles))
    if args.index is not None:
        selected = [selected[args.index]]
    if args.h is not None:
        selected = [(i, p) for i, p in selected if p[0] == args.h]

    if args.write_dimacs is not None and len(selected) != 1:
        parser.error("--write-dimacs requires --index or a filter selecting one profile")

    for index, (h, counts) in selected:
        start = time.monotonic()
        solver = coupled_solver(
            h,
            counts,
            int(1000 * args.timeout),
            coupling=not args.no_coupling,
            omit_block=args.defect_only,
            omit_defect=args.block_only,
            full_graph=args.full_graph,
            h2_split=tuple(args.h2_split) if args.h2_split is not None else None,
        )
        if args.write_dimacs is not None:
            goal = z3.Goal()
            goal.add(*solver.assertions())
            cnf = z3.Then(
                "simplify", "propagate-values", "card2bv", "bit-blast", "tseitin-cnf"
            )(goal)
            if len(cnf) != 1:
                raise RuntimeError(f"CNF lowering returned {len(cnf)} subgoals")
            args.write_dimacs.write_text(cnf[0].dimacs())
            elapsed = time.monotonic() - start
            print(
                f"{index:02d} h={h:2d} counts={counts} "
                f"clauses={len(cnf[0])} dimacs={args.write_dimacs} {elapsed:.2f}s",
                flush=True,
            )
            continue
        result = solver.check()
        elapsed = time.monotonic() - start
        print(f"{index:02d} h={h:2d} counts={counts} {result} {elapsed:.2f}s", flush=True)


if __name__ == "__main__":
    main()
