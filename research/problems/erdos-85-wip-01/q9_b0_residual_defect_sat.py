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

The mixed common-center constraint can be ablated in two algebraically useful
pieces: ``dtb-aq-cap`` is the entrywise bound ``A_T Q <= 1``, while
``dtb-orthogonal`` is the disjoint-support law ``(A_T Q) * (Q K) = 0``.
For fixed outer witnesses tested on 2026-08-21, the orthogonality law alone
(with defect variables decoupled via ``dtb-zero``) remained UNSAT in about two
seconds in both branches; the AQ cap alone timed out.  This is localization,
not a certificate or a universal UNSAT claim.  A second split showed that
orthogonality together with the B0 Gram law (blocks sharing a U1 point cannot
share a residual center) remains UNSAT even after removing the ordinary
residual C4 constraint; removing both Gram laws gives SAT witnesses.

The ``--audit-hole-partitions-seeds`` mode isolates the equality case behind
that fast UNSAT result.  For each exceptional triple center ``h``, its six
residual-neighbor blocks would have to be three triples and three pairs that
partition the complement of ``supp(Q_h K)``.  The mode counts such local
partitions in independently generated outer witnesses.  Zero counts are
external evidence for a prospective uniform lemma, not a proof that every
outer design has this property.

The ``--hole-partition-only`` mode asks the corresponding seed-free question:
it keeps the unrestricted outer ``Q,K`` design and only the residual edges
incident to exceptional holes.  It imposes the six-neighbor/three-triple
equality case, trace orthogonality, and the B0 Gram no-shared-neighbor law,
without constructing the other residual rows.  An UNSAT result would still
need independent certification; a timeout is only an open computational
frontier.
Use ``--hole-partition-at-least K`` to weaken the question to any ``K`` of
the exceptional holes; this distinguishes a per-hole obstruction from one
that only appears after coupling the complete hole set.
"""

from __future__ import annotations

import argparse
import subprocess
import tempfile
import time
from itertools import combinations
from pathlib import Path

from z3 import And, Bool, Goal, If, Not, Or, SolverFor, Sum, Then, is_true, sat, unknown


N_TRIPLE = 26
N_PAIR = 21
N = N_TRIPLE + N_PAIR


def edge_key(u: int, v: int) -> tuple[int, int]:
    assert u != v
    return (u, v) if u < v else (v, u)


N_U1 = 24


def color(v: int) -> int:
    return v // 8


def build(branch: int, timeout_ms: int, full_incidence: bool,
          outer_seed: dict | None = None,
          relax: set[str] | None = None) -> tuple[Solver, dict]:
    if branch not in (3, 4):
        raise ValueError("branch must be 3 or 4")
    holes = 2 if branch == 3 else 4
    classes = N_TRIPLE - holes
    relax = relax or set()
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
        if "row-ledger" not in relax:
            solver.add(degree == (6 if is_hole(u) or u >= N_TRIPLE else 5))
        triple_neighbors = Sum([If(adj(u, v), 1, 0) for v in range(N_TRIPLE) if v != u])
        for g, support in enumerate(pair_groups):
            miss[u, g] = Bool(f"miss_{u}_{g}")
            solver.add(miss[u, g] == (Sum([If(adj(u, v), 1, 0) for v in support]) == 0))
        marked_defect = Sum([If(miss[u, g], 1, 0) for g in range(3)])
        if "row-ledger" in relax:
            continue
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
        if "residual-c4" not in relax:
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
        # Match the lossless normalization in the outer model: the first
        # full class is the eight diagonal color triples.
        for u in range(8):
            diagonal = {u, 8 + u, 16 + u}
            for b in range(N_U1):
                solver.add(incidence[u, b] == (b in diagonal))
        for g, centers in enumerate(pair_groups):
            for b in range(N_U1):
                solver.add(Sum([If(incidence[u, b], 1, 0) for u in centers]) <= 1)

        # Project the B0--B1 defect column equations before introducing the
        # residual graph.  Degree-six incident blocks are the three marked
        # pair groups and the exceptional holes; branch 4 gains one for each
        # punctured special class missed.
        for b in range(N_U1):
            pair_count = Sum([If(incidence[u, b], 1, 0)
                              for u in range(N_TRIPLE, N)])
            hole_count = Sum([If(incidence[u, b], 1, 0)
                              for u in range(classes, N_TRIPLE)])
            if branch == 3:
                solver.add(pair_count + hole_count == 2)
            else:
                missed = Sum([
                    If(Sum([If(incidence[u, b], 1, 0)
                            for u in class_ranges[r]]) == 0, 1, 0)
                    for r in (1, 2)
                ])
                solver.add(pair_count + hole_count == 2 + missed)

        if outer_seed is not None:
            for u, block in enumerate(outer_seed["blocks"]):
                block = set(block)
                for b in range(N_U1):
                    solver.add(incidence[u, b] == (b in block))

        # Two B0 centers cannot have two common U1 points; an existing U1
        # common point also consumes their residual common-neighbor allowance.
        for u, v in combinations(range(N), 2):
            block_common = Sum([If(And(incidence[u, b], incidence[v, b]), 1, 0) for b in range(N_U1)])
            residual_common = Sum([If(adj(u, w) & adj(v, w), 1, 0) for w in range(N) if w not in (u, v)])
            if "b0-c4" not in relax:
                solver.add(block_common <= 1)
                if "b0-orthogonal" not in relax:
                    solver.add(Or(block_common == 0, residual_common == 0))

        # Cubic U1 graph: one neighbor of every high color at every point.
        k = {edge_key(a, b): Bool(f"k_{a}_{b}") for a, b in combinations(range(N_U1), 2)}

        def kadj(a: int, b: int):
            return False if a == b else k[edge_key(a, b)]

        for a in range(N_U1):
            for c in range(3):
                solver.add(Sum([If(kadj(a, b), 1, 0) for b in range(N_U1) if b != a and color(b) == c]) == 1)
        first_color_matching = {(0, 1), (2, 3), (4, 5), (6, 7)}
        for a, b in combinations(range(8), 2):
            solver.add(k[edge_key(a, b)] ==
                       (edge_key(a, b) in first_color_matching))
        if outer_seed is not None:
            fixed_k = {edge_key(*e) for e in outer_seed["k_edges"]}
            for e, var in k.items():
                solver.add(var == (e in fixed_k))

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
                core_common = [And(incidence[u, c], kadj(c, b))
                               for c in range(N_U1) if c != b]
                residual_common = [And(adj(u, v), incidence[v, b])
                                   for v in range(N) if v != u]
                core_count = Sum([If(q, 1, 0) for q in core_common])
                residual_count = Sum([If(q, 1, 0) for q in residual_common])
                common_count = core_count + residual_count
                if "dtb-common" not in relax and "dtb-cap" not in relax:
                    if "dtb-aq-cap" not in relax:
                        solver.add(residual_count <= 1)
                    if "dtb-orthogonal" not in relax:
                        solver.add(Or(core_count == 0, residual_count == 0))
                if "dtb-common" not in relax and "dtb-zero" not in relax:
                    solver.add(dtb[u, b] == (common_count == 0))
            target = 0 if is_hole(u) else 3
            if "dtb-rows" not in relax:
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
            if "dtb-columns" not in relax:
                solver.add(Sum([If(dtb[u, b], 1, 0) for u in range(N)]) + special == 5)

    return solver, {"edges": edges, "miss": miss, "classes": classes,
                    "incidence": incidence, "k": k, "defect_u1": defect_u1}


def make_outer_seed(branch: int, timeout_ms: int, random_seed: int = 0,
                    require_eligible_hole_pair: bool = False) -> dict:
    """Obtain one fast 24-core witness and canonically index its 47 blocks."""
    import q9_three_high_u1_design_sat as outer

    solver, data = outer.build(branch, timeout_ms)
    if require_eligible_hole_pair:
        witnesses = []
        for t, u in combinations(data["triples"], 2):
            if not set(t) & set(u):
                continue
            no_cross_core_edge = [
                Not(data["k"][edge_key(a, b)])
                for a in t for b in u if a != b]
            witnesses.append(And(data["holes"][t], data["holes"][u],
                                 *no_cross_core_edge))
        solver.add(Or(witnesses))
    solver.set(random_seed=random_seed)
    result = solver.check()
    if result != sat:
        raise RuntimeError(f"outer design did not solve: {result}")
    model = solver.model()

    def chosen(mapping):
        return sorted(key for key, var in mapping.items()
                      if is_true(model.eval(var, model_completion=True)))

    blocks = []
    for class_map in data["classes"]:
        blocks.extend(chosen(class_map))
    blocks.extend(chosen(data["holes"]))
    marked = chosen(data["marked_pairs"])
    for missing_color in range(3):
        group = [e for e in marked
                 if missing_color not in {color(e[0]), color(e[1])}]
        if len(group) != 7:
            raise RuntimeError(f"bad marked group {missing_color}: {len(group)}")
        blocks.extend(group)
    if len(blocks) != N:
        raise RuntimeError(f"bad outer block count: {len(blocks)}")
    return {"blocks": blocks, "k_edges": chosen(data["k"])}


def hole_partition_counts(branch: int, timeout_ms: int,
                          random_seed: int) -> list[int]:
    """Count equality-case neighbor-block partitions at every hole."""
    seed = make_outer_seed(branch, timeout_ms, random_seed)
    blocks = [set(block) for block in seed["blocks"]]
    k_neighbors = [set() for _ in range(N_U1)]
    for a, b in seed["k_edges"]:
        k_neighbors[a].add(b)
        k_neighbors[b].add(a)
    core_support = [
        set().union(*(k_neighbors[b] for b in block)) for block in blocks
    ]
    holes = 2 if branch == 3 else 4
    counts = []
    for h in range(N_TRIPLE - holes, N_TRIPLE):
        complement = set(range(N_U1)) - core_support[h]

        def eligible(v: int) -> bool:
            # The first condition is trace orthogonality at h; the second is
            # the same condition at v, needed because the residual edge is
            # symmetric.
            return (v != h and blocks[v] <= complement
                    and not (blocks[h] & core_support[v]))

        triple_candidates = [v for v in range(N_TRIPLE) if eligible(v)]
        pair_candidates = [v for v in range(N_TRIPLE, N) if eligible(v)]
        triple_packings = []
        for chosen in combinations(triple_candidates, 3):
            union = set().union(*(blocks[v] for v in chosen))
            if len(union) == 9:
                triple_packings.append(union)
        pair_packings = []
        for chosen in combinations(pair_candidates, 3):
            union = set().union(*(blocks[v] for v in chosen))
            if len(union) == 6:
                pair_packings.append(union)
        counts.append(sum(
            1 for triples in triple_packings for pairs in pair_packings
            if not (triples & pairs) and triples | pairs == complement
        ))
    return counts


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--branch", type=int, choices=(3, 4), required=True)
    parser.add_argument("--timeout-seconds", type=int, default=300)
    parser.add_argument("--full-incidence", action="store_true")
    parser.add_argument("--seed-outer", action="store_true",
                        help="fix incidence/K to one fast outer-design witness")
    parser.add_argument("--outer-random-seed", type=int, default=0)
    parser.add_argument("--audit-hole-partitions-seeds", type=int, default=0,
                        help="count local exceptional-hole complement partitions "
                             "for seeds 0..N-1, then exit")
    parser.add_argument("--hole-partition-only", action="store_true",
                        help="ask the unrestricted outer model whether every "
                             "exceptional hole can realize its required local "
                             "complement partition")
    parser.add_argument("--hole-partition-at-least", type=int, default=0,
                        help="ask whether at least K exceptional holes can "
                             "realize the local partition (implies the "
                             "seed-free hole-partition-only abstraction)")
    parser.add_argument("--relax", action="append", default=[],
                        choices=("residual-c4", "b0-c4", "b0-orthogonal",
                                 "dtb-common", "dtb-cap", "dtb-aq-cap",
                                 "dtb-orthogonal", "dtb-zero", "dtb-rows",
                                 "dtb-columns", "row-ledger"))
    parser.add_argument("--kissat", action="store_true",
                        help="bit-blast the model to DIMACS and run Kissat")
    args = parser.parse_args()
    if args.audit_hole_partitions_seeds:
        for seed_number in range(args.audit_hole_partitions_seeds):
            counts = hole_partition_counts(
                args.branch, args.timeout_seconds * 1000, seed_number
            )
            print(f"branch={args.branch} outer_seed={seed_number} "
                  f"hole_partition_counts={counts}")
        return 0
    seed = make_outer_seed(args.branch, args.timeout_seconds * 1000,
                           args.outer_random_seed) if args.seed_outer else None
    relax = set(args.relax)
    hole_partition_mode = (args.hole_partition_only
                           or args.hole_partition_at_least > 0)
    if hole_partition_mode:
        if args.seed_outer:
            parser.error("hole-partition queries use the unrestricted outer model")
        relax.update({"row-ledger", "residual-c4", "dtb-aq-cap",
                      "dtb-zero", "dtb-rows", "dtb-columns"})
    solver, data = build(args.branch, args.timeout_seconds * 1000,
                         args.full_incidence or args.seed_outer
                         or hole_partition_mode,
                         seed, relax)
    if hole_partition_mode:
        edges = data["edges"]
        holes = 2 if args.branch == 3 else 4
        required = holes if args.hole_partition_only else args.hole_partition_at_least
        if not 1 <= required <= holes:
            parser.error(f"hole partition count must lie in 1..{holes}")
        active = []
        for h in range(N_TRIPLE - holes, N_TRIPLE):
            active_h = Bool(f"active_hole_partition_{h}")
            active.append(active_h)
            incident = [var for (u, v), var in edges.items()
                        if u == h or v == h]
            triple_incident = [var for (u, v), var in edges.items()
                               if (u == h and v < N_TRIPLE)
                               or (v == h and u < N_TRIPLE)]
            solver.add(Or(Not(active_h),
                          Sum([If(var, 1, 0) for var in incident]) == 6))
            solver.add(Or(Not(active_h),
                          Sum([If(var, 1, 0)
                               for var in triple_incident]) == 3))
        solver.add(Sum([If(flag, 1, 0) for flag in active]) >= required)
    started = time.time()
    if args.kissat:
        goal = Goal()
        goal.add(*solver.assertions())
        cnf_started = time.time()
        transformed = Then("simplify", "solve-eqs", "lia2card", "card2bv",
                           "bit-blast", "tseitin-cnf")(goal)
        cnf_elapsed = time.time() - cnf_started
        if len(transformed) != 1:
            raise RuntimeError(f"CNF tactic produced {len(transformed)} goals")
        dimacs = transformed[0].dimacs()
        with tempfile.TemporaryDirectory(prefix="q9-b0-cnf-") as tmp:
            cnf_path = Path(tmp) / "model.cnf"
            cnf_path.write_text(dimacs)
            proc = subprocess.run(
                ["kissat", f"--time={args.timeout_seconds}", str(cnf_path)],
                text=True, capture_output=True, check=False,
            )
        elapsed = time.time() - started
        status = next((line for line in proc.stdout.splitlines()
                       if line.startswith("s ")), "s UNKNOWN")
        print(f"branch={args.branch} kissat={status[2:]} elapsed={elapsed:.3f}s "
              f"cnf_seconds={cnf_elapsed:.3f} "
              f"vars_clauses={dimacs.splitlines()[0]}")
        return 0 if status != "s UNKNOWN" else 2
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
