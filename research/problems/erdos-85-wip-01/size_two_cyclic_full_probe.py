#!/usr/bin/env python3
"""Full base-dependent SIZE-TWO-EIGENLINE feasibility probe.

Unlike ``size_two_cyclic_translation_invariant_probe.py``, this script has
one undirected Boolean edge for every pair of allowed cells.  It directly
encodes exact target-row/column hits, all same-fibre codegree caps, and an
optional empty fibre.
"""

from __future__ import annotations

import argparse
from itertools import combinations

import z3


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("q", type=int)
    parser.add_argument("--a", type=int, required=True)
    parser.add_argument("--empty-fiber", type=int)
    parser.add_argument("--no-caps", action="store_true")
    parser.add_argument("--drop-row-hits", action="store_true",
        help="diagnostic: omit exact target-row constraints")
    parser.add_argument("--drop-column-hits", action="store_true",
        help="diagnostic: omit exact absolute-column constraints")
    parser.add_argument("--uniform-fibre-loads", action="store_true",
        help="require every target to have exactly one neighbour in each source fibre")
    parser.add_argument("--minimal-block-variance", "--sharp-fibre-loads",
        dest="minimal_block_variance", action="store_true",
        help="give each source one zero, one double, and otherwise one target per fibre")
    parser.add_argument("--dump-fibre-loads", action="store_true",
        help="on SAT, print target-fibre degree profiles for every source")
    parser.add_argument("--dump-route-table", action="store_true",
        help="on SAT, print each source's exact target-base to fibre routes")
    parser.add_argument("--min-sharp-sources", type=int,
        help="require at least this many sources to have a 0,2,1,... block profile")
    parser.add_argument("--max-total-defect-rank", type=int,
        help="bound the total number of zero source-to-fibre loads")
    parser.add_argument("--require-reflection-rank-imbalance", type=int,
        nargs=2, metavar=("X", "T"),
        help="require unequal zero-load counts at (x,t) and (x,-1-t)")
    parser.add_argument("--require-odd-sharp-count-at-base", type=int,
        metavar="X", help="require an odd number of rank-one sources at base x")
    parser.add_argument("--max-nonsharp-at-adjacent-bases", type=int, nargs=2,
        metavar=("X", "N"),
        help="bound rank-at-least-two sources at bases x and x+1")
    parser.add_argument("--max-defect-rank-at-adjacent-bases", type=int,
        nargs=2, metavar=("X", "N"),
        help="bound total zero-load count at bases x and x+1")
    parser.add_argument("--max-parity-missing-at-adjacent-bases", type=int,
        nargs=2, action="append", metavar=("X", "N"),
        help="bound zero loads into fibres u congruent to x mod 2 at x,x+1")
    parser.add_argument("--min-parity-missing-at-adjacent-bases", type=int,
        nargs=2, action="append", metavar=("X", "N"),
        help="lower-bound parity-selected zero loads at x,x+1")
    parser.add_argument("--global-route-sign", choices=("even", "odd"),
        help="require the product sign of all local row-to-column permutations")
    parser.add_argument("--directed", action="store_true",
        help="drop reciprocity and use one variable per ordered pair")
    parser.add_argument("--reciprocity-core", action="store_true",
        help="use directed variables and shrink reciprocity by fibre-pair groups")
    parser.add_argument("--reciprocity-fibre-pair", type=int, nargs=2,
        action="append", metavar=("T", "U"),
        help="with --reciprocity-core, activate only the listed fibre pairs")
    parser.add_argument("--joint-group-core", action="store_true",
        help="shrink reciprocity blocks and full-cap families together")
    parser.add_argument("--joint-separation-core", action="store_true",
        help="shrink reciprocity blocks and cap fibre/separation groups")
    parser.add_argument("--dump-internal-profile", action="store_true",
        help="on SAT, print internal edges and occupied bases in each fibre")
    parser.add_argument("--dump-collision-separations", action="store_true",
        help="on SAT, summarize same-fibre common targets by base separation")
    parser.add_argument("--dump-collision-owner-fibres", action="store_true",
        help="on SAT, also resolve collision summaries by common-target fibre")
    parser.add_argument("--dump-sharp-edge-census", action="store_true",
        help="on SAT, summarize edges and sharp-neighbour degrees by source profile")
    parser.add_argument("--dump-adjacent-boundary-layers", action="store_true",
        help="on SAT, print routes from every base x to target base x+1")
    parser.add_argument("--dump-parity-window-surplus", type=int, metavar="X",
        help="on SAT, decompose PMR at bases x,x+1 by source")
    parser.add_argument("--dump-parity-charge", action="store_true",
        help="on SAT, print per-base rank, parity charge, and all PMR surpluses")
    parser.add_argument("--dump-slot-cuts", action="store_true",
        help="on SAT, print internal/boundary and defect counts for every PMR slot cut")
    parser.add_argument("--dump-pmr-color-transition", action="store_true",
        help="on SAT, print the reciprocal slot graph between PMR window colors")
    parser.add_argument("--require-pmr-color-transition-imbalance", type=int,
        nargs=2, metavar=("C", "D"),
        help="require one PMR color-transition entry to differ from its antipode")
    parser.add_argument("--require-any-pmr-color-transition-imbalance",
        action="store_true",
        help="require the PMR color-transition matrix not to be antipodal")
    parser.add_argument("--minimize-cap-excess", action="store_true",
        help="in --no-caps mode, minimize total common-target excess over one")
    parser.add_argument("--max-cap-excess", type=int,
        help="in --no-caps mode, bound total common-target excess over one")
    parser.add_argument("--require-internal-fibres", action="store_true",
        help="require at least one internal edge or arc in every allowed fibre")
    parser.add_argument("--require-internal-full-support", action="store_true",
        help="require every base to have an internal neighbour in its fibre")
    parser.add_argument("--require-internal-perfect-matching", action="store_true",
        help="require every base to have exactly one internal neighbour")
    parser.add_argument("--max-internal-edges", type=int,
        help="bound the total number of undirected internal-fibre edges")
    parser.add_argument("--force-internal-two-path", type=int, nargs=4,
        metavar=("T", "X", "Y", "Z"),
        help="force the internal edges x-y and y-z in fibre t")
    parser.add_argument("--only-cap-pair", type=int, nargs=3,
        metavar=("T", "X", "Z"),
        help="impose only the common-target cap for bases x,z in fibre t")
    parser.add_argument("--cap-fibres", type=int, nargs="+",
        help="impose full pair caps only in the listed endpoint fibres")
    parser.add_argument("--timeout-ms", type=int, default=300_000)
    parser.add_argument("--random-seed", type=int, default=0,
        help="Z3 random seed for reproducible witness sampling")
    parser.add_argument("--dimacs")
    args = parser.parse_args()

    if sum((args.directed, args.reciprocity_core, args.joint_group_core,
            args.joint_separation_core)) > 1:
        parser.error("directed/core modes are mutually exclusive")
    if (args.reciprocity_core or args.joint_group_core or
            args.joint_separation_core) and args.dimacs is not None:
        parser.error("core modes cannot be combined with --dimacs")
    if (args.reciprocity_fibre_pair is not None and
            not args.reciprocity_core):
        parser.error("--reciprocity-fibre-pair requires --reciprocity-core")
    if args.no_caps and args.only_cap_pair is not None:
        parser.error("--no-caps and --only-cap-pair are incompatible")
    if args.drop_row_hits and args.drop_column_hits:
        parser.error("cannot drop both exact-hit families")
    if args.dump_route_table and args.drop_row_hits:
        parser.error("--dump-route-table requires exact target-row hits")
    if args.dump_slot_cuts and (args.directed or args.reciprocity_core or
            args.joint_group_core or args.joint_separation_core):
        parser.error("--dump-slot-cuts requires the reciprocal undirected model")
    if (args.dump_pmr_color_transition or
            args.require_pmr_color_transition_imbalance is not None or
            args.require_any_pmr_color_transition_imbalance) and (
            args.directed or args.reciprocity_core or args.joint_group_core or
            args.joint_separation_core):
        parser.error("PMR color-transition diagnostics require undirected reciprocity")
    if (args.require_pmr_color_transition_imbalance is not None and
            args.require_any_pmr_color_transition_imbalance):
        parser.error("choose a specific or any PMR color-transition imbalance")
    if args.global_route_sign is not None and (
            args.drop_row_hits or args.drop_column_hits):
        parser.error("--global-route-sign requires both exact-hit families")
    if args.no_caps and args.cap_fibres is not None:
        parser.error("--no-caps and --cap-fibres are incompatible")
    if args.only_cap_pair is not None and args.cap_fibres is not None:
        parser.error("--only-cap-pair and --cap-fibres are incompatible")
    if args.minimize_cap_excess and not args.no_caps:
        parser.error("--minimize-cap-excess requires --no-caps")
    if args.max_cap_excess is not None and not args.no_caps:
        parser.error("--max-cap-excess requires --no-caps")
    if args.max_cap_excess is not None and args.max_cap_excess < 0:
        parser.error("--max-cap-excess must be nonnegative")
    if (args.minimize_cap_excess or args.max_cap_excess is not None) and \
            args.dimacs is not None:
        parser.error("cap-excess diagnostics currently require native Z3")
    if args.minimize_cap_excess and (args.reciprocity_core or
            args.joint_group_core or args.joint_separation_core):
        parser.error("--minimize-cap-excess is incompatible with core modes")

    q = args.q
    holes = {args.a % q, (-1 - args.a) % q}
    differences = [t for t in range(q) if t not in holes]
    vertices = [(x, t) for x in range(q) for t in differences]
    vertex_set = set(vertices)
    variables: dict[tuple[tuple[int, int], tuple[int, int]], z3.BoolRef] = {}

    def edge(left: tuple[int, int], right: tuple[int, int]) -> z3.BoolRef:
        if left == right:
            return z3.BoolVal(False)
        key = ((left, right) if (args.directed or args.reciprocity_core or
                                 args.joint_group_core or
                                 args.joint_separation_core)
               else tuple(sorted((left, right))))
        if key not in variables:
            (x, t), (y, u) = key
            variables[key] = z3.Bool(f"e_{x}_{t}_{y}_{u}")
        return variables[key]

    solver = z3.Optimize() if args.minimize_cap_excess else z3.Solver()
    reciprocity_assumptions: list[z3.BoolRef] = []
    cap_assumptions: dict[object, z3.BoolRef] = {}

    if (args.reciprocity_core or args.joint_group_core or
            args.joint_separation_core):
        for i, t in enumerate(differences):
            for u in differences[i:]:
                label = z3.Bool(f"recip_{t}_{u}")
                reciprocity_assumptions.append(label)
                equations = [
                    edge((x, t), (y, u)) == edge((y, u), (x, t))
                    for x in range(q) for y in range(q)
                    if (x, t) != (y, u)
                ]
                solver.add(z3.Implies(label, z3.And(equations)))

    # Exact target-row hits: the two neighbours of (x,t) on its own cyclic
    # component would lie in absolute rows x+t and x+t+1, so those rows are
    # holes and every other target row is hit once.
    if not args.drop_row_hits:
        for source in vertices:
            x, t = source
            for y in range(q):
                wanted = 0 if y in {(x + t) % q, (x + t + 1) % q} else 1
                solver.add(z3.PbEq(
                    [(edge(source, (y, u)), 1) for u in differences], wanted))

    # Exact target-column hits.  A cell (y,u) has absolute second coordinate
    # y+u.  Columns x and x-1 are the two component-neighbour holes.
    if not args.drop_column_hits:
        for source in vertices:
            x, _ = source
            for c in range(q):
                wanted = 0 if c in {x, (x - 1) % q} else 1
                targets = [((c - u) % q, u) for u in differences]
                assert all(target in vertex_set for target in targets)
                solver.add(z3.PbEq(
                    [(edge(source, target), 1) for target in targets], wanted))

    # Row and column offsets both lie in R=Z/q\{0,1}.  In normal-form
    # coordinates the target of labels (r,s) is
    # ((x+t+r), -t-r-s).  The XOR of all inversions s_i>s_j is the sign bit
    # of the local permutation; XOR over every source is its product sign.
    if args.global_route_sign is not None:
        labels = list(range(2, q))
        inversions = []
        for source in vertices:
            x, t = source
            for left_index, r_left in enumerate(labels):
                for r_right in labels[left_index + 1:]:
                    for s_left in labels:
                        for s_right in labels:
                            if s_left <= s_right:
                                continue
                            u_left = (-t - r_left - s_left) % q
                            u_right = (-t - r_right - s_right) % q
                            if (u_left not in differences or
                                    u_right not in differences):
                                continue
                            target_left = ((x + t + r_left) % q, u_left)
                            target_right = ((x + t + r_right) % q, u_right)
                            inversions.append(z3.And(
                                edge(source, target_left),
                                edge(source, target_right)))
        while len(inversions) > 1:
            inversions = [
                z3.Xor(inversions[index], inversions[index + 1])
                if index + 1 < len(inversions) else inversions[index]
                for index in range(0, len(inversions), 2)
            ]
        solver.add(inversions[0] == (args.global_route_sign == "odd"))

    # Equality case of the labelled collision-load bound.  For a fixed
    # source fibre t, its q vertices send q(q-2) incidences into exactly
    # q(q-2) targets.  Requiring every target load to be one is equivalent
    # to zero same-fibre collision energy, and in particular gives full
    # internal support.
    if args.uniform_fibre_loads:
        for t in differences:
            for target in vertices:
                solver.add(z3.PbEq([
                    (edge((x, t), target), 1) for x in range(q)
                ], 1))

    # Smallest positive block-load variance compatible with total degree:
    # one target fibre is missed, one is hit twice, and all others once.
    if args.minimal_block_variance or args.min_sharp_sources is not None:
        sharp_source_flags = []
        for source in vertices:
            sharp = z3.Bool(f"sharp_source_{source[0]}_{source[1]}")
            sharp_source_flags.append((sharp, 1))
            zero_flags = []
            double_flags = []
            for u in differences:
                zero = z3.Bool(f"sharp_zero_{source[0]}_{source[1]}_{u}")
                double = z3.Bool(
                    f"sharp_double_{source[0]}_{source[1]}_{u}")
                zero_flags.append((zero, 1))
                double_flags.append((double, 1))
                terms = [(edge(source, (y, u)), 1) for y in range(q)]
                solver.add(z3.Implies(zero,
                                      z3.And(sharp, z3.PbEq(terms, 0))))
                solver.add(z3.Implies(double,
                                      z3.And(sharp, z3.PbEq(terms, 2))))
                solver.add(z3.Implies(
                    z3.And(sharp, z3.Not(zero), z3.Not(double)),
                    z3.PbEq(terms, 1)))
                solver.add(z3.Not(z3.And(zero, double)))
            solver.add(z3.Implies(sharp, z3.PbEq(zero_flags, 1)))
            solver.add(z3.Implies(sharp, z3.PbEq(double_flags, 1)))
        if args.minimal_block_variance:
            solver.add(z3.PbEq(sharp_source_flags, len(vertices)))
        if args.min_sharp_sources is not None:
            if not 0 <= args.min_sharp_sources <= len(vertices):
                parser.error("--min-sharp-sources is outside the source range")
            solver.add(z3.PbGe(sharp_source_flags,
                               args.min_sharp_sources))

    # For a source p, put e_p(u)=b_p(u)-1.  Since every b_p(u) is
    # nonnegative and sum_u e_p(u)=0, its total positive defect mass equals
    # its total negative defect mass, which is exactly the number of fibres
    # with b_p(u)=0.  This Boolean encoding therefore measures
    # sum_p sum_u max(e_p(u),0) without auxiliary arithmetic variables.
    if args.max_total_defect_rank is not None:
        total_slots = len(vertices) * len(differences)
        if not 0 <= args.max_total_defect_rank <= total_slots:
            parser.error("--max-total-defect-rank is outside the slot range")
        defect_zero_flags = []
        for source in vertices:
            for u in differences:
                zero = z3.Bool(
                    f"defect_zero_{source[0]}_{source[1]}_{u}")
                terms = [(edge(source, (y, u)), 1) for y in range(q)]
                solver.add(zero == z3.PbEq(terms, 0))
                defect_zero_flags.append((zero, 1))
        solver.add(z3.PbLe(defect_zero_flags,
                           args.max_total_defect_rank))

    def source_defect_rank_expr(source: tuple[int, int]) -> z3.ArithRef:
        return z3.Sum([
            z3.If(z3.Sum([
                z3.If(edge(source, (y, u)), 1, 0)
                for y in range(q)]) == 0, 1, 0)
            for u in differences])

    def source_is_sharp_expr(source: tuple[int, int]) -> z3.BoolRef:
        return source_defect_rank_expr(source) == 1

    if args.require_reflection_rank_imbalance is not None:
        x, t = (value % q for value in
                args.require_reflection_rank_imbalance)
        reflected_t = (-1 - t) % q
        if t not in differences or reflected_t not in differences:
            parser.error("the requested fibre or its reflection is a hole")

        solver.add(source_defect_rank_expr((x, t)) !=
                   source_defect_rank_expr((x, reflected_t)))

    if args.require_odd_sharp_count_at_base is not None:
        x = args.require_odd_sharp_count_at_base % q

        sharp_parity = z3.BoolVal(False)
        for t in differences:
            sharp_parity = z3.Xor(sharp_parity,
                                  source_is_sharp_expr((x, t)))
        solver.add(sharp_parity)

    if args.max_nonsharp_at_adjacent_bases is not None:
        x, maximum = args.max_nonsharp_at_adjacent_bases
        x %= q
        if not 0 <= maximum <= 2 * len(differences):
            parser.error("adjacent-base nonsharp bound is outside its range")
        solver.add(z3.PbLe([
            (z3.Not(source_is_sharp_expr((base, t))), 1)
            for base in (x, (x + 1) % q) for t in differences
        ], maximum))

    if args.max_defect_rank_at_adjacent_bases is not None:
        x, maximum = args.max_defect_rank_at_adjacent_bases
        x %= q
        if not 0 <= maximum <= 2 * len(differences) ** 2:
            parser.error("adjacent-base defect-rank bound is outside its range")
        solver.add(z3.PbLe([
            (z3.Sum([
                z3.If(edge((base, t), (y, u)), 1, 0)
                for y in range(q)]) == 0, 1)
            for base in (x, (x + 1) % q)
            for t in differences for u in differences
        ], maximum))

    if args.max_parity_missing_at_adjacent_bases is not None:
        for x, maximum in args.max_parity_missing_at_adjacent_bases:
            x %= q
            parity_fibres = [u for u in differences if u % 2 == x % 2]
            if q % 2 != 0:
                parser.error("the parity-selected diagnostic requires even q")
            if not 0 <= maximum <= 2 * len(differences) * len(parity_fibres):
                parser.error("parity-selected missing bound is outside its range")
            solver.add(z3.PbLe([
                (z3.Sum([
                    z3.If(edge((base, t), (y, u)), 1, 0)
                    for y in range(q)]) == 0, 1)
                for base in (x, (x + 1) % q)
                for t in differences for u in parity_fibres
            ], maximum))

    if args.min_parity_missing_at_adjacent_bases is not None:
        for x, minimum in args.min_parity_missing_at_adjacent_bases:
            x %= q
            parity_fibres = [u for u in differences if u % 2 == x % 2]
            if q % 2 != 0:
                parser.error("the parity-selected diagnostic requires even q")
            if not 0 <= minimum <= 2 * len(differences) * len(parity_fibres):
                parser.error("parity-selected missing bound is outside its range")
            solver.add(z3.PbGe([
                (z3.Sum([
                    z3.If(edge((base, t), (y, u)), 1, 0)
                    for y in range(q)]) == 0, 1)
                for base in (x, (x + 1) % q)
                for t in differences for u in parity_fibres
            ], minimum))

    # Full same-difference cap: any two distinct bases in one fibre have at
    # most one precise common target cell.
    if not args.no_caps:
        for t in differences:
            if (args.cap_fibres is not None and
                    t not in {value % q for value in args.cap_fibres}):
                continue
            if args.joint_group_core:
                cap_assumptions[t] = z3.Bool(f"caps_{t}")
            for x, z in combinations(range(q), 2):
                if args.only_cap_pair is not None:
                    selected = tuple(value % q for value in args.only_cap_pair)
                    if (t, x, z) != (selected[0], min(selected[1:]),
                                     max(selected[1:])):
                        continue
                left, right = (x, t), (z, t)
                constraint = z3.PbLe([
                    (z3.And(edge(left, target), edge(right, target)), 1)
                    for target in vertices
                ], 1)
                if args.joint_group_core or args.joint_separation_core:
                    if args.joint_group_core:
                        key: object = t
                    else:
                        raw = (z - x) % q
                        key = (t, min(raw, (-raw) % q))
                        if key not in cap_assumptions:
                            cap_assumptions[key] = z3.Bool(
                                f"cap_{key[0]}_{key[1]}")
                    solver.add(z3.Implies(cap_assumptions[key], constraint))
                else:
                    solver.add(constraint)

    if args.empty_fiber is not None:
        t = args.empty_fiber % q
        if t not in differences:
            parser.error(f"empty fibre {t} is forbidden by the two holes")
        base_pairs = ((x, z) for x in range(q) for z in range(q) if x != z)
        if not (args.directed or args.reciprocity_core or
                args.joint_group_core or args.joint_separation_core):
            base_pairs = combinations(range(q), 2)
        for x, z in base_pairs:
            solver.add(z3.Not(edge((x, t), (z, t))))

    if args.require_internal_fibres:
        for t in differences:
            if args.directed:
                candidates = [edge((x, t), (z, t))
                              for x in range(q) for z in range(q) if x != z]
            else:
                candidates = [edge((x, t), (z, t))
                              for x, z in combinations(range(q), 2)]
            solver.add(z3.Or(candidates))

    if args.require_internal_full_support:
        for t in differences:
            for x in range(q):
                solver.add(z3.Or([
                    edge((x, t), (z, t)) for z in range(q) if z != x
                ]))

    if args.require_internal_perfect_matching:
        for t in differences:
            for x in range(q):
                solver.add(z3.PbEq([
                    (edge((x, t), (z, t)), 1)
                    for z in range(q) if z != x
                ], 1))

    if (args.require_pmr_color_transition_imbalance is not None or
            args.require_any_pmr_color_transition_imbalance):
        half = q // 2

        def color(base: int, target_fibre: int) -> int:
            return base if base % 2 == target_fibre % 2 else (base - 1) % q

        def transition_expr(left_color: int, right_color: int) -> z3.ArithRef:
            terms = []
            for left, right in combinations(vertices, 2):
                (x, t), (y, u) = left, right
                lc, rc = color(x, u), color(y, t)
                coefficient = int(lc == left_color and rc == right_color)
                coefficient += int(rc == left_color and lc == right_color)
                if coefficient:
                    terms.append(z3.If(edge(left, right), coefficient, 0))
            return z3.Sum(terms)

        if args.require_pmr_color_transition_imbalance is not None:
            c, d = (value % q for value in
                    args.require_pmr_color_transition_imbalance)
            solver.add(transition_expr(c, d) != transition_expr(
                (c + half) % q, (d + half) % q))
        else:
            solver.add(z3.Or([
                transition_expr(c, d) != transition_expr(
                    (c + half) % q, (d + half) % q)
                for c in range(half) for d in range(q)
            ]))

    if args.max_internal_edges is not None:
        if (args.directed or args.reciprocity_core or args.joint_group_core or
                args.joint_separation_core):
            parser.error("--max-internal-edges requires undirected mode")
        solver.add(z3.PbLe([
            (edge((x, t), (z, t)), 1)
            for t in differences for x, z in combinations(range(q), 2)
        ], args.max_internal_edges))

    if args.force_internal_two_path is not None:
        t, x, y, z = (value % q for value in args.force_internal_two_path)
        if t not in differences or len({x, y, z}) != 3:
            parser.error("forced two-path needs an allowed fibre and distinct bases")
        solver.add(edge((x, t), (y, t)), edge((y, t), (z, t)))

    cap_excess_objective = None
    if args.minimize_cap_excess or args.max_cap_excess is not None:
        excess_terms = []
        for t in differences:
            for x, z in combinations(range(q), 2):
                common = z3.Sum([
                    z3.If(z3.And(edge((x, t), target),
                                 edge((z, t), target)), 1, 0)
                    for target in vertices
                ])
                excess_terms.append(z3.If(common > 1, common - 1, 0))
        cap_excess_objective = z3.Sum(excess_terms)
        if args.max_cap_excess is not None:
            solver.add(cap_excess_objective <= args.max_cap_excess)
        if args.minimize_cap_excess:
            solver.minimize(cap_excess_objective)

    if args.dimacs is not None:
        goal = z3.Goal()
        goal.add(*solver.assertions())
        transformed = z3.Then(
            "simplify", "card2bv", "bit-blast", "tseitin-cnf")(goal)
        if len(transformed) != 1:
            raise RuntimeError("CNF conversion unexpectedly produced subgoals")
        for clause in transformed[0]:
            literals = clause.children() if z3.is_or(clause) else [clause]
            for literal in literals:
                atom = literal.arg(0) if z3.is_not(literal) else literal
                if (z3.is_true(atom) or z3.is_false(atom) or
                        (z3.is_const(atom) and atom.sort() == z3.BoolSort() and
                         atom.decl().kind() == z3.Z3_OP_UNINTERPRETED)):
                    continue
                raise RuntimeError(
                    f"CNF conversion left an opaque theory atom: {atom}")
        cnf_solver = z3.Solver()
        cnf_solver.add(*transformed[0])
        with open(args.dimacs, "w", encoding="ascii") as output:
            output.write(cnf_solver.dimacs())
        print(f"q={q} vertices={len(vertices)} edge_variables={len(variables)}: "
              f"wrote {args.dimacs}")
        return

    solver.set(timeout=args.timeout_ms)
    solver.set(random_seed=args.random_seed)
    active_assumptions = reciprocity_assumptions + list(cap_assumptions.values())
    if args.reciprocity_fibre_pair is not None:
        selected_pairs = {
            tuple(sorted((t % q, u % q)))
            for t, u in args.reciprocity_fibre_pair
        }
        if any(t not in differences or u not in differences
               for pair in selected_pairs for t, u in [pair]):
            parser.error("selected reciprocity pair contains a hole fibre")
        selected_labels = {f"recip_{t}_{u}" for t, u in selected_pairs}
        active_assumptions = [label for label in active_assumptions
                              if str(label) in selected_labels]
    result = solver.check(*active_assumptions)
    print(f"q={q} a={args.a % q} vertices={len(vertices)} "
          f"edge_variables={len(variables)}: {result}")
    if result == z3.sat and args.dump_internal_profile:
        model = solver.model()
        for t in differences:
            if args.directed:
                internal = [
                    (x, z) for x in range(q) for z in range(q) if x != z
                    if z3.is_true(model.eval(
                        edge((x, t), (z, t)), model_completion=True))
                ]
                occupied = sorted({x for x, _ in internal})
                print(f"  internal fibre={t} arcs={len(internal)} "
                      f"occupied_sources={len(occupied)} "
                      f"source_bases={occupied}")
            else:
                internal = [
                    (x, z) for x, z in combinations(range(q), 2)
                    if z3.is_true(model.eval(
                        edge((x, t), (z, t)), model_completion=True))
                ]
                occupied = sorted({base for pair in internal for base in pair})
                degrees = [sum(base in pair for pair in internal)
                           for base in range(q)]
                print(f"  internal fibre={t} edges={len(internal)} "
                      f"occupied_bases={len(occupied)} bases={occupied} "
                      f"degrees={degrees}")
    if result == z3.sat and args.dump_collision_separations:
        model = solver.model()
        if cap_excess_objective is not None:
            print("  minimum_cap_excess=" +
                  str(model.eval(cap_excess_objective).as_long()))
        for t in differences:
            summary: dict[int, list[int]] = {}
            for x, z in combinations(range(q), 2):
                common = sum(z3.is_true(model.eval(
                    z3.And(edge((x, t), target), edge((z, t), target)),
                    model_completion=True)) for target in vertices)
                raw = (z - x) % q
                separation = min(raw, (-raw) % q)
                data = summary.setdefault(separation, [0, 0, 0, 0])
                data[0] += 1
                data[1] += common
                data[2] += common > 0
                data[3] += max(0, common - 1)
            for separation, (pairs, mass, occupied, excess) in sorted(
                    summary.items()):
                print(f"  collision fibre={t} separation={separation} "
                      f"pairs={pairs} mass={mass} occupied={occupied} "
                      f"cap_excess={excess}")
    if result == z3.sat and args.dump_collision_owner_fibres:
        model = solver.model()
        for t in differences:
            summary: dict[tuple[int, int], list[int]] = {}
            for x, z in combinations(range(q), 2):
                raw = (z - x) % q
                separation = min(raw, (-raw) % q)
                for u in differences:
                    common = sum(z3.is_true(model.eval(z3.And(
                        edge((x, t), (y, u)), edge((z, t), (y, u))),
                        model_completion=True)) for y in range(q))
                    data = summary.setdefault((u, separation), [0, 0, 0])
                    data[0] += common
                    data[1] += common > 0
                    data[2] += max(0, common - 1)
            for (u, separation), (mass, occupied, excess) in sorted(
                    summary.items()):
                if mass:
                    print(f"  collision endpoint_fibre={t} owner_fibre={u} "
                          f"separation={separation} mass={mass} "
                          f"occupied={occupied} within_owner_excess={excess}")
    if result == z3.sat and args.dump_sharp_edge_census:
        model = solver.model()
        sharp: dict[tuple[int, int], bool] = {}
        for source in vertices:
            loads = [sum(z3.is_true(model.eval(
                edge(source, (y, u)), model_completion=True))
                for y in range(q)) for u in differences]
            sharp[source] = (loads.count(0) == 1 and loads.count(2) == 1
                             and all(load in {0, 1, 2} for load in loads))
        edge_counts = {"SS": 0, "SN": 0, "NN": 0}
        sharp_neighbour_degrees = {True: [], False: []}
        same_status_adjacency = {source: set() for source in vertices}
        for source in vertices:
            sharp_neighbour_degrees[sharp[source]].append(sum(
                z3.is_true(model.eval(edge(source, target),
                                      model_completion=True)) and sharp[target]
                for target in vertices if target != source))
        for left, right in combinations(vertices, 2):
            if not z3.is_true(model.eval(edge(left, right),
                                         model_completion=True)):
                continue
            key = "SS" if sharp[left] and sharp[right] else (
                "NN" if not sharp[left] and not sharp[right] else "SN")
            edge_counts[key] += 1
            if sharp[left] == sharp[right]:
                same_status_adjacency[left].add(right)
                same_status_adjacency[right].add(left)
        print(f"  sharp_sources={sum(sharp.values())} edge_census={edge_counts}")
        for is_sharp, degrees in sharp_neighbour_degrees.items():
            histogram = {degree: degrees.count(degree)
                         for degree in sorted(set(degrees))}
            print(f"  source_class={'sharp' if is_sharp else 'nonsharp'} "
                  f"sharp_neighbour_degree_histogram={histogram}")
            unseen = {source for source in vertices
                      if sharp[source] == is_sharp}
            component_sizes = []
            while unseen:
                stack = [unseen.pop()]
                size = 0
                while stack:
                    source = stack.pop()
                    size += 1
                    fresh = same_status_adjacency[source] & unseen
                    unseen.difference_update(fresh)
                    stack.extend(fresh)
                component_sizes.append(size)
            print(f"  source_class={'sharp' if is_sharp else 'nonsharp'} "
                  f"component_sizes={sorted(component_sizes, reverse=True)}")
    if result == z3.sat and args.dump_adjacent_boundary_layers:
        model = solver.model()
        for x in range(q):
            target_base = (x + 1) % q
            layer = []
            for t in differences:
                hits = [u for u in differences if z3.is_true(model.eval(
                    edge((x, t), (target_base, u)),
                    model_completion=True))]
                if len(hits) > 1:
                    raise RuntimeError(
                        f"adjacent boundary row {(x, t)} has {len(hits)} hits")
                if hits:
                    layer.append((t, hits[0]))
            print(f"  adjacent_boundary={x}->{target_base} routes={layer}")
    if result == z3.sat and args.dump_parity_window_surplus is not None:
        model = solver.model()
        x = args.dump_parity_window_surplus % q
        selected = {u for u in differences if u % 2 == x % 2}
        total_rank = 0
        total_selected_zeros = 0
        total_selected_excess = 0
        total_surplus = 0
        for base in (x, (x + 1) % q):
            for t in differences:
                loads = {u: sum(z3.is_true(model.eval(
                    edge((base, t), (y, u)), model_completion=True))
                    for y in range(q)) for u in differences}
                rank = sum(load == 0 for load in loads.values())
                selected_zeros = sum(loads[u] == 0 for u in selected)
                selected_excess = sum(max(0, loads[u] - 1)
                                      for u in selected)
                sharp = (rank == 1 and list(loads.values()).count(2) == 1
                         and all(load in {0, 1, 2}
                                 for load in loads.values()))
                surplus = selected_zeros + selected_excess - 1
                total_rank += rank
                total_selected_zeros += selected_zeros
                total_selected_excess += selected_excess
                total_surplus += surplus
                print(f"  parity_window={x} source={(base, t)} "
                      f"rank={rank} sharp={sharp} "
                      f"selected_zeros={selected_zeros} "
                      f"selected_excess={selected_excess} "
                      f"surplus={surplus}")
        print(f"  parity_window={x} total_rank={total_rank} "
              f"selected_zeros={total_selected_zeros} "
              f"selected_excess={total_selected_excess} "
              f"surplus={total_surplus}")
    if result == z3.sat and args.dump_parity_charge:
        model = solver.model()
        ranks = []
        same = []
        opposite = []
        for base in range(q):
            rank = 0
            same_missing = 0
            opposite_missing = 0
            for t in differences:
                loads = {u: sum(z3.is_true(model.eval(
                    edge((base, t), (y, u)), model_completion=True))
                    for y in range(q)) for u in differences}
                missing = [u for u in differences if loads[u] == 0]
                rank += len(missing)
                same_missing += sum(u % 2 == base % 2 for u in missing)
                opposite_missing += sum(u % 2 != base % 2 for u in missing)
            ranks.append(rank)
            same.append(same_missing)
            opposite.append(opposite_missing)
        charge = [same[x] - opposite[x] for x in range(q)]
        selected = [same[x] + opposite[(x + 1) % q]
                    for x in range(q)]
        surplus = [2 * selected[x] - 2 * (q - 2) for x in range(q)]
        print(f"  parity_charge ranks={ranks} same={same} "
              f"opposite={opposite} charge={charge} "
              f"selected={selected} surplus={surplus}")
    if result == z3.sat and args.dump_slot_cuts:
        model = solver.model()
        loads = {}
        for source in vertices:
            for u in differences:
                loads[(source, u)] = sum(z3.is_true(model.eval(
                    edge(source, (y, u)), model_completion=True))
                    for y in range(q))
        selected_edges = [
            (left, right) for left, right in combinations(vertices, 2)
            if z3.is_true(model.eval(edge(left, right),
                                     model_completion=True))
        ]
        for x in range(q):
            bases = {x, (x + 1) % q}
            parity = x % 2

            def in_cut(source, target_fibre):
                return source[0] in bases and target_fibre % 2 == parity

            internal_edges = []
            boundary = 0
            for left, right in selected_edges:
                left_in = in_cut(left, right[1])
                right_in = in_cut(right, left[1])
                if left_in and right_in:
                    internal_edges.append((left, right))
                boundary += left_in != right_in
            cut_loads = [load for (source, u), load in loads.items()
                         if in_cut(source, u)]
            isolated = sum(load == 0 for load in cut_loads)
            occupied = sum(load > 0 for load in cut_loads)
            excess = sum(max(0, load - 1) for load in cut_loads)
            degree_sum = sum(cut_loads)
            diagonal_internal = sum(left[1] == right[1]
                                    for left, right in internal_edges)
            print(f"  slot_cut={x} internal={len(internal_edges)} "
                  f"diagonal_internal={diagonal_internal} "
                  f"internal_edges={internal_edges} boundary={boundary} "
                  f"isolated={isolated} occupied={occupied} excess={excess} "
                  f"degree_sum={degree_sum}")
    if result == z3.sat and args.dump_pmr_color_transition:
        model = solver.model()

        def pmr_color(base: int, target_fibre: int) -> int:
            return base if base % 2 == target_fibre % 2 else (base - 1) % q

        transition = [[0 for _ in range(q)] for _ in range(q)]
        for left, right in combinations(vertices, 2):
            if not z3.is_true(model.eval(edge(left, right),
                                         model_completion=True)):
                continue
            (x, t), (y, u) = left, right
            left_color = pmr_color(x, u)
            right_color = pmr_color(y, t)
            transition[left_color][right_color] += 1
            transition[right_color][left_color] += 1

        histograms = []
        for color in range(q):
            degrees = []
            for base, t in vertices:
                for u in differences:
                    if pmr_color(base, u) != color:
                        continue
                    degrees.append(sum(z3.is_true(model.eval(
                        edge((base, t), (y, u)), model_completion=True))
                        for y in range(q)))
            histogram = {degree: degrees.count(degree)
                         for degree in sorted(set(degrees))}
            histograms.append(histogram)
        half = q // 2
        antipodal = all(
            transition[x][y] == transition[(x + half) % q][(y + half) % q]
            for x in range(q) for y in range(q))
        print(f"  pmr_color_transition antipodal={antipodal}")
        for color in range(q):
            print(f"  pmr_color={color} transition={transition[color]} "
                  f"degree_histogram={histograms[color]}")
    if result == z3.sat and args.dump_fibre_loads:
        model = solver.model()
        for source in vertices:
            loads = [sum(z3.is_true(model.eval(
                edge(source, (y, u)), model_completion=True))
                for y in range(q)) for u in differences]
            print(f"  source={source} loads={dict(zip(differences, loads))}")
    if result == z3.sat and args.dump_route_table:
        model = solver.model()
        for source in vertices:
            routes = {
                y: next(u for u in differences if z3.is_true(model.eval(
                    edge(source, (y, u)), model_completion=True)))
                for y in range(q)
                if any(z3.is_true(model.eval(edge(source, (y, u)),
                                             model_completion=True))
                       for u in differences)
            }
            print(f"  source={source} routes={routes}")
    if result == z3.unsat and (args.reciprocity_core or args.joint_group_core or
                               args.joint_separation_core):
        core = list(solver.unsat_core())
        # Directed relaxations encountered while deleting a block can be
        # substantially harder than the reciprocal instance.  UNKNOWN keeps
        # the block, so this bound preserves a sufficient (if nonminimal)
        # core and prevents one diagnostic from becoming a solver campaign.
        solver.set(timeout=5_000)
        if args.joint_separation_core:
            # First delete whole cap fibres.  Removing their separation
            # labels one at a time can turn an easy group deletion into a
            # hard near-feasible query and obscure the smaller fibre core.
            for t in differences:
                prefix = f"cap_{t}_"
                candidate = [item for item in core
                             if not str(item).startswith(prefix)]
                if solver.check(*candidate) == z3.unsat:
                    core = candidate
        for label in list(core):
            candidate = [other for other in core if not z3.eq(other, label)]
            if solver.check(*candidate) == z3.unsat:
                core = candidate
        solver.check(*core)
        label = ("joint_group_core" if args.joint_group_core else
                 "joint_separation_core" if args.joint_separation_core else
                 "reciprocity_core")
        print(f"  {label}=" + str(sorted(str(item) for item in core)))


if __name__ == "__main__":
    main()
