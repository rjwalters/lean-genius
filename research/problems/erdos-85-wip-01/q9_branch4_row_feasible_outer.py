#!/usr/bin/env python3
"""Generate branch-4 outer designs on the fractional row-feasible locus.

The ordinary random outer-design sweep is a poor test of the proposed
global-special load selector: almost every generated design already has a
strict one-row point cover.  This script adds the *dual* condition for every
row directly to the outer SMT instance.  For each selected row ``u`` it asks
for a fractional packing on mutually trace-eligible candidate rows ``v`` such that

    sum_v w[u,v] >= d(u),
    sum_{v : p in B_v} w[u,v] <= 1  for every U1 point p.

By fractional LP duality this is exactly the assertion that the selected
row's minimum one-row point-cover cost is at least ``d(u)``.  The fast default
selects the four exceptional rows; the emitted payload is then independently
rechecked on all 47 rows with the rational LP auditor in
``q9_symmetric_point_mass_obstruction.py``; this file is an exploratory
generator, not a proof certificate.
"""

from __future__ import annotations

import argparse
import json
from functools import cache
from itertools import combinations
from pathlib import Path

from z3 import And, Bool, If, Implies, Int, Not, Or, Sum, is_true, sat

from q9_b0_residual_defect_sat import N, N_TRIPLE, N_U1, build, edge_key
from q9_symmetric_point_mass_obstruction import (
    OUTER_ONLY_RELAX, fixed_system, unit_row_cover_optimum,
)


def build_row_feasible(timeout_seconds: int, denominator: int,
                       rows: list[int], shared_integral_relation: bool,
                       exclude_single_special_hole: bool,
                       all_incident_disjoint_packings: bool,
                       all_conflicting_disjoint_packings: bool,
                       requested_disjoint_pairs: list[tuple[int, int]],
                       all_reciprocity_compatible_packings: bool,
                       reciprocity_pairs: list[tuple[int, int]],
                       reverse_interval_rows: list[int],
                       requested_integral_rows: list[int],
                       fixed_template_primal_denominator: int | None,
                       template: dict | None = None):
    solver, data = build(
        4, timeout_seconds * 1000, True, outer_seed=template,
        relax=OUTER_ONLY_RELAX
    )

    incidence = data["incidence"]
    k = data["k"]

    if exclude_single_special_hole:
        punctured_classes = (range(8, 15), range(15, 22))
        for hole in range(22, 26):
            for point in range(N_U1):
                hits = [
                    Or([incidence[row, point] for row in rows])
                    for rows in punctured_classes
                ]
                solver.add(Implies(
                    incidence[hole, point], hits[0] == hits[1]
                ))

    def kadj(a: int, b: int):
        return False if a == b else k[edge_key(a, b)]

    @cache
    def core(row: int, point: int):
        return Or([
            And(incidence[row, source], kadj(source, point))
            for source in range(N_U1) if source != point
        ])

    @cache
    def eligible(u: int, v: int):
        return And([
            Implies(incidence[v, point], Not(core(u, point)))
            for point in range(N_U1)
        ])

    @cache
    def mutually_eligible(u: int, v: int):
        return And(eligible(u, v), eligible(v, u))

    if fixed_template_primal_denominator is not None:
        scale = fixed_template_primal_denominator
        for regular in range(22):
            for hole in range(22, 26):
                candidate_edges = [
                    edge_key(u, v)
                    for u in (regular, hole) for v in range(N) if u != v
                ]
                candidate_edges = sorted(set(candidate_edges))
                weight = {
                    edge: Int(
                        f"fixed_template_primal_{regular}_{hole}_"
                        f"{edge[0]}_{edge[1]}"
                    )
                    for edge in candidate_edges
                }
                for (u, v), value in weight.items():
                    solver.add(value >= 0, value <= scale)
                    solver.add(Implies(Not(mutually_eligible(u, v)), value == 0))

                def edge_weight(u: int, v: int):
                    if u == v:
                        return 0
                    return weight.get(edge_key(u, v), 0)

                # Point-price variables on the two supported rows yield the
                # two independent block-packing capacity systems.
                for supported in (regular, hole):
                    for point in range(N_U1):
                        solver.add(Sum([
                            If(incidence[v, point], edge_weight(supported, v), 0)
                            for v in range(N) if v != supported
                        ]) <= scale)
                # If the named blocks meet at p, the permitted incoming price
                # z[v,p] couples the two incident edge weights at every third
                # row v.  When they are disjoint there is no such constraint.
                for v in range(N):
                    if v in (regular, hole):
                        continue
                    for point in range(N_U1):
                        solver.add(Implies(
                            And(incidence[regular, point],
                                incidence[hole, point]),
                            edge_weight(v, regular) + edge_weight(v, hole)
                                <= scale,
                        ))
                solver.add(Sum([
                    ((int(regular in edge) + 2 * int(hole in edge)) * value)
                    for edge, value in weight.items()
                ]) >= 17 * scale)

    disjoint_pairs = {edge_key(u, v) for u, v in requested_disjoint_pairs}
    if all_incident_disjoint_packings:
        disjoint_pairs.update(
            (regular, hole)
            for regular in range(22) for hole in range(22, 26)
        )
    if all_conflicting_disjoint_packings:
        disjoint_pairs.update(combinations(range(N), 2))
    for regular, hole in sorted(disjoint_pairs):
        incident = Or([
            And(incidence[regular, point], incidence[hole, point])
            for point in range(N_U1)
        ])
        first = {
            v: Bool(f"joint_pack_regular_{regular}_{hole}_{v}")
            for v in range(N)
        }
        second = {
            v: Bool(f"joint_pack_hole_{regular}_{hole}_{v}")
            for v in range(N)
        }
        solver.add(Implies(
            incident, Sum([If(first[v], 1, 0) for v in range(N)]) ==
                (6 if regular >= N_TRIPLE - 4 else 5)
        ))
        solver.add(Implies(
            incident, Sum([If(second[v], 1, 0) for v in range(N)]) ==
                (6 if hole >= N_TRIPLE - 4 else 5)
        ))
        for v in range(N):
            solver.add(Implies(first[v], And(
                incident, regular != v,
                eligible(regular, v), eligible(v, regular),
            )))
            solver.add(Implies(second[v], And(
                incident, hole != v,
                eligible(hole, v), eligible(v, hole),
            )))
            solver.add(Not(And(first[v], second[v])))
        for point in range(N_U1):
            solver.add(Implies(incident, Sum([
                If(And(first[v], incidence[v, point]), 1, 0)
                for v in range(N)
            ]) <= 1))
            solver.add(Implies(incident, Sum([
                If(And(second[v], incidence[v, point]), 1, 0)
                for v in range(N)
            ]) <= 1))

    requested_reciprocity_pairs = set(reciprocity_pairs)
    if all_reciprocity_compatible_packings:
        requested_reciprocity_pairs.update(
            (u, w) for u in range(N) for w in range(N) if u != w
        )
    for u, w in sorted(requested_reciprocity_pairs):
        avoid_branch = Bool(f"reciprocity_avoid_branch_{u}_{w}")
        avoid = {
            v: Bool(f"reciprocity_avoid_{u}_{w}_{v}")
            for v in range(N)
        }
        reverse = {
            v: Bool(f"reciprocity_reverse_{u}_{w}_{v}")
            for v in range(N)
        }
        solver.add(Implies(avoid_branch, Sum([
            If(avoid[v], 1, 0) for v in range(N)
        ]) == (6 if u >= N_TRIPLE - 4 else 5)))
        solver.add(Implies(Not(avoid_branch), Sum([
            If(reverse[v], 1, 0) for v in range(N)
        ]) == (6 if w >= N_TRIPLE - 4 else 5)))
        solver.add(Not(avoid[w]))
        solver.add(Implies(Not(avoid_branch), reverse[u]))
        for v in range(N):
            solver.add(Implies(avoid[v], And(
                avoid_branch, u != v,
                eligible(u, v), eligible(v, u),
            )))
            solver.add(Implies(reverse[v], And(
                Not(avoid_branch), w != v,
                eligible(w, v), eligible(v, w),
            )))
        for point in range(N_U1):
            solver.add(Implies(avoid_branch, Sum([
                If(And(avoid[v], incidence[v, point]), 1, 0)
                for v in range(N)
            ]) <= 1))
            solver.add(Implies(Not(avoid_branch), Sum([
                If(And(reverse[v], incidence[v, point]), 1, 0)
                for v in range(N)
            ]) <= 1))

    # A reverse-interval witness at `target` is the exact negation of the
    # one-row compatibility obstruction used by the Lean consumer.  Select
    # one full packing X at target.  For every other source u, select a full
    # local packing Y_u whose target-membership bit agrees with u ∈ X.
    # This simultaneously realizes the whole reverse-forced lower bundle and
    # avoids the reverse-impossible upper bundle; unlike pairwise reciprocity,
    # all bits must agree with one common target packing.
    for target in sorted(set(reverse_interval_rows)):
        target_selected = {
            v: Bool(f"reverse_interval_target_{target}_{v}")
            for v in range(N) if v != target
        }
        target_degree = 6 if target >= N_TRIPLE - 4 else 5
        solver.add(Sum([
            If(target_selected[v], 1, 0) for v in target_selected
        ]) == target_degree)
        for v, selected in target_selected.items():
            solver.add(Implies(selected, And(
                eligible(target, v), eligible(v, target),
            )))
        for point in range(N_U1):
            solver.add(Sum([
                If(And(target_selected[v], incidence[v, point]), 1, 0)
                for v in target_selected
            ]) <= 1)

        for source in range(N):
            if source == target:
                continue
            reverse = {
                v: Bool(
                    f"reverse_interval_source_{target}_{source}_{v}"
                )
                for v in range(N) if v != source
            }
            source_degree = 6 if source >= N_TRIPLE - 4 else 5
            solver.add(Sum([
                If(reverse[v], 1, 0) for v in reverse
            ]) == source_degree)
            solver.add(reverse[target] == target_selected[source])
            for v, selected in reverse.items():
                solver.add(Implies(selected, And(
                    eligible(source, v), eligible(v, source),
                )))
            for point in range(N_U1):
                solver.add(Sum([
                    If(And(reverse[v], incidence[v, point]), 1, 0)
                    for v in reverse
                ]) <= 1)

    for u in sorted(set(requested_integral_rows)):
        selected = {
            v: Bool(f"integral_row_pack_{u}_{v}") for v in range(N)
        }
        solver.add(Sum([
            If(selected[v], 1, 0) for v in range(N)
        ]) == (6 if u >= N_TRIPLE - 4 else 5))
        for v in range(N):
            solver.add(Implies(selected[v], And(
                u != v, eligible(u, v), eligible(v, u),
            )))
        for point in range(N_U1):
            solver.add(Sum([
                If(And(selected[v], incidence[v, point]), 1, 0)
                for v in range(N)
            ]) <= 1)

    if shared_integral_relation:
        relation = {
            (u, v): Bool(f"shared_relation_{u}_{v}")
            for u in range(N) for v in range(u + 1, N)
        }

        def rel(u: int, v: int):
            return False if u == v else relation[min(u, v), max(u, v)]

        for u in range(N):
            degree = 6 if u >= N_TRIPLE - 4 else 5
            solver.add(Sum([
                If(rel(u, v), 1, 0) for v in range(N) if v != u
            ]) == degree)
            for point in range(N_U1):
                solver.add(Sum([
                    If(And(rel(u, v), incidence[v, point]), 1, 0)
                    for v in range(N) if v != u
                ]) <= 1)
        for u in range(N):
            for v in range(u + 1, N):
                solver.add(Implies(rel(u, v), And(
                    eligible(u, v), eligible(v, u)
                )))

    packing = {}
    for u in rows:
        for v in range(N):
            if u == v:
                continue
            # A bounded common denominator keeps the augmented instance in
            # QF_FD.  This is stronger than unrestricted fractional row
            # feasibility, but every SAT model is a valid fractional model.
            weight = (If(Bool(f"row_pack_bool_{u}_{v}"), 1, 0)
                      if denominator == 1 else Int(f"row_pack_{u}_{v}"))
            packing[u, v] = weight
            if denominator != 1:
                solver.add(weight >= 0, weight <= denominator)
            solver.add(Implies(
                Not(And(eligible(u, v), eligible(v, u))), weight == 0
            ))

        degree = 6 if u >= N_TRIPLE - 4 else 5
        solver.add(Sum([packing[u, v] for v in range(N) if v != u]) >=
                   denominator * degree)
        for point in range(N_U1):
            solver.add(Sum([
                If(incidence[v, point], packing[u, v], 0)
                for v in range(N) if v != u
            ]) <= denominator)

    return solver, data


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--timeout-seconds", type=int, default=600)
    parser.add_argument("--random-seed", type=int, default=0)
    parser.add_argument("--denominator", type=int, default=12)
    parser.add_argument(
        "--template", type=Path,
        help="fix the outer design to a payload (encoding regression mode)",
    )
    parser.add_argument(
        "--rows", type=int, nargs="*", default=list(range(22, 26)),
        help=("rows whose fractional feasibility is imposed; defaults to "
              "the four exceptional branch-4 holes 22..25"),
    )
    parser.add_argument(
        "--all-rows", action="store_true",
        help="impose the packing condition on all 47 rows",
    )
    parser.add_argument(
        "--shared-integral-relation", action="store_true",
        help=("also synthesize one common symmetric 0/1 relation with all "
              "row degrees, mutual eligibility, and point capacities"),
    )
    parser.add_argument(
        "--exclude-single-special-hole", action="store_true",
        help=("forbid every hole point from being missed by exactly one "
              "punctured class"),
    )
    parser.add_argument(
        "--all-incident-disjoint-packings", action="store_true",
        help=("attempt to refute (13as) by requiring every incident "
              "regular/exceptional pair to admit disjoint integral local "
              "block-packings of sizes five and six"),
    )
    parser.add_argument(
        "--all-conflicting-disjoint-packings", action="store_true",
        help=("require every block-intersecting row pair to admit disjoint "
              "integral local packings of its actual demanded sizes"),
    )
    parser.add_argument(
        "--disjoint-pair", type=int, nargs=2, action="append", default=[],
        metavar=("U", "V"),
        help="require disjoint full local packings at one conflicting pair",
    )
    parser.add_argument(
        "--all-reciprocity-compatible-packings", action="store_true",
        help=("for every ordered row pair (u,w), require either a full "
              "packing at u avoiding w or a full packing at w containing u"),
    )
    parser.add_argument(
        "--reciprocity-pair", type=int, nargs=2, action="append", default=[],
        metavar=("U", "W"),
        help="impose the reciprocity-compatible disjunction only at (u,w)",
    )
    parser.add_argument(
        "--reverse-interval-row", type=int, action="append", default=[],
        help=("require one target packing whose membership bits are all "
              "realizable by corresponding reverse local packings"),
    )
    parser.add_argument(
        "--integral-row", type=int, action="append", default=[],
        help="require one full integral local packing at the named row",
    )
    parser.add_argument(
        "--all-pairs-fixed-template-primal-denominator", type=int,
        help=("attempt to refute (13at): for every exceptional/regular pair, "
              "require a bounded-denominator dual packing of weighted value "
              "at least 17, thereby negating its fixed (1,2) strict cover"),
    )
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()

    if args.denominator <= 0:
        parser.error("--denominator must be positive")
    if (args.all_pairs_fixed_template_primal_denominator is not None
            and args.all_pairs_fixed_template_primal_denominator <= 0):
        parser.error(
            "--all-pairs-fixed-template-primal-denominator must be positive"
        )
    rows = list(range(N)) if args.all_rows else args.rows
    if any(row < 0 or row >= N for row in rows):
        parser.error("--rows entries must lie in 0..46")
    reciprocity_pairs = [tuple(pair) for pair in args.reciprocity_pair]
    disjoint_pairs = [tuple(pair) for pair in args.disjoint_pair]
    if any(u < 0 or u >= N or v < 0 or v >= N or u == v
           for u, v in disjoint_pairs):
        parser.error("--disjoint-pair requires distinct rows in 0..46")
    if any(u < 0 or u >= N or w < 0 or w >= N or u == w
           for u, w in reciprocity_pairs):
        parser.error("--reciprocity-pair requires distinct rows in 0..46")
    if any(u < 0 or u >= N for u in args.integral_row):
        parser.error("--integral-row entries must lie in 0..46")
    if any(u < 0 or u >= N for u in args.reverse_interval_row):
        parser.error("--reverse-interval-row entries must lie in 0..46")
    template = json.loads(args.template.read_text()) if args.template else None
    solver, data = build_row_feasible(
        args.timeout_seconds, args.denominator, rows,
        args.shared_integral_relation, args.exclude_single_special_hole,
        args.all_incident_disjoint_packings,
        args.all_conflicting_disjoint_packings,
        disjoint_pairs,
        args.all_reciprocity_compatible_packings,
        reciprocity_pairs,
        args.reverse_interval_row,
        args.integral_row,
        args.all_pairs_fixed_template_primal_denominator,
        template=template
    )
    solver.set(random_seed=args.random_seed)
    result = solver.check()
    print(f"row_feasible_outer={result}")
    if result != sat:
        return
    model = solver.model()
    payload = {
        "branch": 4,
        "blocks": [
            [point for point in range(N_U1)
             if is_true(model.eval(data["incidence"][row, point],
                                   model_completion=True))]
            for row in range(N)
        ],
        "k_edges": [
            list(edge) for edge, variable in data["k"].items()
            if is_true(model.eval(variable, model_completion=True))
        ],
    }
    system = fixed_system(payload)
    strict_rows = [
        row for row in range(N)
        if unit_row_cover_optimum(system, row)["strict"]
    ]
    print(f"independent_strict_one_row_covers={strict_rows}")
    print(f"all_rows_fractionally_feasible={not strict_rows}")
    encoded = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    if args.output is None:
        print(encoded, end="")
    else:
        args.output.write_text(encoded)
        print(f"wrote={args.output}")


if __name__ == "__main__":
    main()
