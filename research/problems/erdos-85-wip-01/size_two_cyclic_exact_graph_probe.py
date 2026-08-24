#!/usr/bin/env python3
"""Direct SAT probe for the graph-free SIZE-TWO-EIGENLINE(q) object.

Vertices are the allowed cells (x,y), with y-x outside the two holes
{a,-1-a}.  By default we ask directly for a simple graph satisfying the exact
row and column hit laws and the common-neighbour cap.  ``--allow-loops`` keeps
the diagonal of the symmetric relation, modelling the reduced reciprocal code
before Loopless is imposed.  The Boolean edge encoding is substantially
smaller than the permutation encoding.
"""

from __future__ import annotations

import argparse
from collections import Counter
from itertools import combinations, combinations_with_replacement

import z3


def build(q: int, a: int, *, rows: bool = True, columns: bool = True,
          c4_pair_mode: str = "all",
          c4_differences: set[int] | None = None,
          c4_separations: set[int] | None = None,
          c4_fiber_separations: set[tuple[int, int]] | None = None,
          allow_loops: bool = False) -> tuple[z3.Solver, list[tuple[int, int]], dict[tuple[int, int], z3.BoolRef]]:
    holes = {a % q, (-1 - a) % q}
    vertices = [(x, y) for x in range(q) for y in range(q) if (y - x) % q not in holes]
    index = {v: i for i, v in enumerate(vertices)}
    edge_indices = (combinations_with_replacement(range(len(vertices)), 2)
                    if allow_loops else combinations(range(len(vertices)), 2))
    edge = {(i, j): z3.Bool(f"e_{i}_{j}") for i, j in edge_indices}

    def adj(i: int, j: int) -> z3.BoolRef:
        if i == j and not allow_loops:
            return z3.BoolVal(False)
        return edge[min(i, j), max(i, j)]

    solver = z3.Solver()

    # Exact row and column hits.  Zero fibers are asserted too: they provide
    # cheap unit propagation before the C4 constraints are introduced.
    for i, (x, y) in enumerate(vertices):
        if rows:
            for row in range(q):
                want = 0 if row in {y, (y + 1) % q} else 1
                solver.add(z3.PbEq([(adj(i, index[row, col]), 1)
                                    for col in range(q) if (row, col) in index], want))
        if columns:
            for col in range(q):
                want = 0 if col in {x, (x - 1) % q} else 1
                solver.add(z3.PbEq([(adj(i, index[row, col]), 1)
                                    for row in range(q) if (row, col) in index], want))

    # C4-free is exactly: distinct vertices have at most one common neighbor.
    if c4_pair_mode != "none":
        for i, j in combinations(range(len(vertices)), 2):
            separation = (vertices[j][0] - vertices[i][0]) % q
            if c4_separations is not None and \
                    separation not in c4_separations and \
                    (-separation) % q not in c4_separations:
                continue
            if c4_pair_mode == "same-row" and vertices[i][0] != vertices[j][0]:
                continue
            if c4_pair_mode == "same-column" and vertices[i][1] != vertices[j][1]:
                continue
            if c4_pair_mode == "same-difference" and \
                    (vertices[i][1] - vertices[i][0]) % q != \
                    (vertices[j][1] - vertices[j][0]) % q:
                continue
            if c4_pair_mode == "same-difference" and c4_differences is not None and \
                    (vertices[i][1] - vertices[i][0]) % q not in c4_differences:
                continue
            if c4_fiber_separations is not None:
                source_difference = (vertices[i][1] - vertices[i][0]) % q
                undirected_separation = min(separation, (-separation) % q)
                if (source_difference, undirected_separation) not in \
                        c4_fiber_separations:
                    continue
            common_neighbor_indices = (range(len(vertices)) if allow_loops else
                                       (k for k in range(len(vertices))
                                        if k not in {i, j}))
            solver.add(z3.PbLe([(z3.And(adj(i, k), adj(j, k)), 1)
                                for k in common_neighbor_indices], 1))

    return solver, vertices, edge


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("q", type=int)
    parser.add_argument("--a", type=int, required=True)
    parser.add_argument("--timeout-ms", type=int, default=300_000)
    parser.add_argument("--no-rows", action="store_true")
    parser.add_argument("--no-columns", action="store_true")
    parser.add_argument("--no-c4", action="store_true")
    parser.add_argument("--c4-pair-mode",
        choices=["all", "same-row", "same-column", "same-difference"],
        default="all")
    parser.add_argument("--c4-difference", type=int, action="append",
        help="with same-difference mode, retain only these difference orbits")
    parser.add_argument("--c4-separation", type=int, action="append",
        help=("retain common-neighbor caps only for these undirected "
              "first-coordinate separation orbits"))
    parser.add_argument("--c4-fiber-separation", action="append",
        help=("retain an individual same-difference cap group, written "
              "DIFFERENCE:SEPARATION; may be repeated"))
    parser.add_argument("--quiet-model", action="store_true")
    parser.add_argument("--codegree-profile-difference", type=int,
        help=("report codegree/excess totals by undirected first-coordinate "
              "separation for source vertices in this difference fiber"))
    parser.add_argument("--codegree-excess-cap", type=int,
        help=("bound the total number of common-neighbor pairs for the "
              "--codegree-profile-difference source fiber"))
    parser.add_argument("--uniform-profile-multiplicity", action="store_true",
        help=("require every vertex to have exactly one neighbor in the "
              "--codegree-profile-difference source fiber"))
    parser.add_argument("--parity-block-profile", action="store_true",
        help=("report oriented route mass by source/target difference parity, "
              "splitting same-parity mass into diagonal and off-diagonal fibers"))
    parser.add_argument("--parity-same-mass-cap", type=int,
        help="upper-bound the oriented route mass in each same-parity block")
    parser.add_argument("--parity-same-mass-floor", type=int,
        help="lower-bound the oriented route mass in each same-parity block")
    parser.add_argument("--cross-collision-profile", action="store_true",
        help=("report cross-fiber incidence products sum_B n_t(B)n_u(B) "
              "for every pair of allowed difference fibers"))
    parser.add_argument("--cross-collision-pair", type=int, nargs=2,
        metavar=("T", "U"),
        help="select two source-difference fibers for a cross-collision bound")
    parser.add_argument("--cross-collision-cap", type=int,
        help="upper-bound the product sum for --cross-collision-pair")
    parser.add_argument("--random-seed", type=int, default=0)
    parser.add_argument("--allow-loops", action="store_true",
        help=("model the reduced symmetric reciprocal relation, whose "
              "diagonal entries are not constrained by Loopless"))
    parser.add_argument("--loop-count-cap", type=int,
        help="bound the total number of chosen diagonal entries")
    parser.add_argument("--loop-profile", action="store_true",
        help="report chosen diagonal entries by difference fiber")
    args = parser.parse_args()
    if args.loop_count_cap is not None and not args.allow_loops:
        parser.error("--loop-count-cap requires --allow-loops")
    if args.loop_profile and not args.allow_loops:
        parser.error("--loop-profile requires --allow-loops")
    fiber_separations = None
    if args.c4_fiber_separation is not None:
        if args.c4_pair_mode != "same-difference":
            parser.error("--c4-fiber-separation requires same-difference mode")
        fiber_separations = set()
        for spec in args.c4_fiber_separation:
            try:
                raw_difference, raw_separation = map(int, spec.split(":"))
            except ValueError:
                parser.error("--c4-fiber-separation must have form DIFFERENCE:SEPARATION")
            separation = raw_separation % args.q
            fiber_separations.add((raw_difference % args.q,
                                   min(separation, (-separation) % args.q)))
    solver, vertices, edge = build(args.q, args.a,
        rows=not args.no_rows, columns=not args.no_columns,
        c4_pair_mode="none" if args.no_c4 else args.c4_pair_mode,
        c4_differences=None if args.c4_difference is None else
            {t % args.q for t in args.c4_difference},
        c4_separations=None if args.c4_separation is None else
            {d % args.q for d in args.c4_separation},
        c4_fiber_separations=fiber_separations,
        allow_loops=args.allow_loops)
    if args.loop_count_cap is not None:
        solver.add(z3.PbLe([(edge[i, i], 1) for i in range(len(vertices))],
                           args.loop_count_cap))
    if (args.codegree_excess_cap is not None or
            args.uniform_profile_multiplicity):
        if args.codegree_profile_difference is None:
            parser.error("codegree constraints require "
                         "--codegree-profile-difference")
        index = {vertex: i for i, vertex in enumerate(vertices)}
        source = [index[vertex] for vertex in vertices
                  if (vertex[1] - vertex[0]) % args.q ==
                  args.codegree_profile_difference % args.q]
        if not source:
            parser.error("profile difference is one of the forbidden fibers")

        def adj_expr(i: int, j: int) -> z3.BoolRef:
            if i == j and not args.allow_loops:
                return z3.BoolVal(False)
            return edge[min(i, j), max(i, j)]

    if args.uniform_profile_multiplicity:
        for j in range(len(vertices)):
            solver.add(z3.PbEq([(adj_expr(i, j), 1) for i in source], 1))

    if args.codegree_excess_cap is not None:
        excess_terms = []
        for i, j in combinations(source, 2):
            common_neighbor_indices = (list(range(len(vertices)))
                                       if args.allow_loops else
                                       [k for k in range(len(vertices))
                                        if k not in {i, j}])
            for k, ell in combinations(common_neighbor_indices, 2):
                excess_terms.append((z3.And(
                    adj_expr(i, k), adj_expr(j, k),
                    adj_expr(i, ell), adj_expr(j, ell)), 1))
        solver.add(z3.PbLe(excess_terms, args.codegree_excess_cap))
    if (args.parity_same_mass_cap is not None or
            args.parity_same_mass_floor is not None):
        for parity in (0, 1):
            terms = []
            for (i, j), var in edge.items():
                source_difference = (vertices[i][1] - vertices[i][0]) % args.q
                target_difference = (vertices[j][1] - vertices[j][0]) % args.q
                if source_difference % 2 == parity and target_difference % 2 == parity:
                    terms.append((var, 1 if i == j else 2))
            if args.parity_same_mass_cap is not None:
                solver.add(z3.PbLe(terms, args.parity_same_mass_cap))
            if args.parity_same_mass_floor is not None:
                solver.add(z3.PbGe(terms, args.parity_same_mass_floor))
    if args.cross_collision_cap is not None:
        if args.cross_collision_pair is None:
            parser.error("--cross-collision-cap requires --cross-collision-pair")
        index = {vertex: i for i, vertex in enumerate(vertices)}
        t, u = (value % args.q for value in args.cross_collision_pair)
        source_t = [index[v] for v in vertices
                    if (v[1] - v[0]) % args.q == t]
        source_u = [index[v] for v in vertices
                    if (v[1] - v[0]) % args.q == u]
        if not source_t or not source_u:
            parser.error("cross-collision pair contains a forbidden fiber")

        def bounded_adj(i: int, j: int) -> z3.BoolRef:
            if i == j and not args.allow_loops:
                return z3.BoolVal(False)
            return edge[min(i, j), max(i, j)]

        terms = []
        for target in range(len(vertices)):
            for i in source_t:
                for j in source_u:
                    terms.append((z3.And(
                        bounded_adj(i, target), bounded_adj(j, target)), 1))
        solver.add(z3.PbLe(terms, args.cross_collision_cap))
    solver.set(timeout=args.timeout_ms, random_seed=args.random_seed)
    result = solver.check()
    print(f"q={args.q} a={args.a % args.q} allow_loops={args.allow_loops}: {result}")
    if result == z3.sat and args.loop_profile:
        model = solver.model()
        loops = [vertices[i] for i in range(len(vertices))
                 if z3.is_true(model.eval(edge[i, i]))]
        profile = Counter((y - x) % args.q for x, y in loops)
        print(f"loop profile: total={len(loops)} "
              f"by_difference={dict(sorted(profile.items()))}")
    if result == z3.sat and args.codegree_profile_difference is not None:
        model = solver.model()
        index = {vertex: i for i, vertex in enumerate(vertices)}

        def chosen_adj(i: int, j: int) -> bool:
            if i == j and not args.allow_loops:
                return False
            return z3.is_true(model.eval(edge[min(i, j), max(i, j)]))

        source = [index[vertex] for vertex in vertices
                  if (vertex[1] - vertex[0]) % args.q ==
                  args.codegree_profile_difference % args.q]
        profile: dict[int, Counter[int]] = {}
        for i, j in combinations(source, 2):
            raw_separation = (vertices[j][0] - vertices[i][0]) % args.q
            separation = min(raw_separation, (-raw_separation) % args.q)
            common_neighbor_indices = (range(len(vertices)) if args.allow_loops
                                       else (k for k in range(len(vertices))
                                             if k not in {i, j}))
            codegree = sum(chosen_adj(i, k) and chosen_adj(j, k)
                           for k in common_neighbor_indices)
            profile.setdefault(separation, Counter())[codegree] += 1
        print("codegree profile by source separation:")
        total_codegree = 0
        total_excess = 0
        for separation, distribution in sorted(profile.items()):
            codegree_sum = sum(value * count
                               for value, count in distribution.items())
            excess = sum(value * (value - 1) // 2 * count
                         for value, count in distribution.items())
            total_codegree += codegree_sum
            total_excess += excess
            print(f"  {separation}: distribution={dict(sorted(distribution.items()))} "
                  f"sum={codegree_sum} excess={excess}")
        print(f"codegree totals: sum={total_codegree} excess={total_excess}")
    if result == z3.sat and args.parity_block_profile:
        model = solver.model()
        block_mass = Counter()
        diagonal_mass = Counter()
        for (i, j), var in edge.items():
            if not z3.is_true(model.eval(var)):
                continue
            source_difference = (vertices[i][1] - vertices[i][0]) % args.q
            target_difference = (vertices[j][1] - vertices[j][0]) % args.q
            source_parity = source_difference % 2
            target_parity = target_difference % 2
            block_mass[source_parity, target_parity] += 1
            if source_difference == target_difference:
                diagonal_mass[source_parity] += 1
            if i != j:
                block_mass[target_parity, source_parity] += 1
                if source_difference == target_difference:
                    diagonal_mass[target_parity] += 1
        print("oriented parity route blocks: "
              f"EE={block_mass[0, 0]} EO={block_mass[0, 1]} "
              f"OE={block_mass[1, 0]} OO={block_mass[1, 1]}")
        print("same-parity split: "
              f"even diagonal={diagonal_mass[0]} "
              f"off-diagonal={block_mass[0, 0] - diagonal_mass[0]}; "
              f"odd diagonal={diagonal_mass[1]} "
              f"off-diagonal={block_mass[1, 1] - diagonal_mass[1]}")
    if result == z3.sat and args.cross_collision_profile:
        model = solver.model()
        index = {vertex: i for i, vertex in enumerate(vertices)}

        def chosen_adj(i: int, j: int) -> bool:
            if i == j and not args.allow_loops:
                return False
            return z3.is_true(model.eval(edge[min(i, j), max(i, j)]))

        differences = sorted({(y - x) % args.q for x, y in vertices})
        fibers = {
            t: [index[v] for v in vertices if (v[1] - v[0]) % args.q == t]
            for t in differences
        }
        incidence = {
            t: [sum(chosen_adj(i, j) for i in fibers[t])
                for j in range(len(vertices))]
            for t in differences
        }
        print("cross-fiber collision products:")
        for t, u in combinations(differences, 2):
            collision = sum(a * b for a, b in zip(incidence[t], incidence[u]))
            print(f"  {t},{u}: {collision}")
    if result == z3.sat and not args.quiet_model:
        model = solver.model()
        chosen = [(vertices[i], vertices[j]) for (i, j), var in edge.items()
                  if z3.is_true(model.eval(var))]
        print(f"vertices={len(vertices)} edges={len(chosen)}")
        for u, v in chosen:
            print(f"  {u} -- {v}")


if __name__ == "__main__":
    main()
