#!/usr/bin/env python3
"""Reduced translation-invariant SIZE-TWO-EIGENLINE probe.

An edge from cell ``(x, x+t)`` to ``(x+r, x+r+u)`` is represented by one
Boolean ``E(t,u,r)``.  Reciprocity identifies ``E(t,u,r)`` with
``E(u,t,-r)``.  The model retains the exact row and column hit laws and can
impose selected same-fiber codegree caps without constructing the full
``q(q-2)``-vertex graph.
"""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict

import z3


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("q", type=int)
    parser.add_argument("--a", type=int, required=True)
    parser.add_argument("--cap", action="append", default=[],
        help="same-fiber codegree cap DIFFERENCE:SEPARATION")
    parser.add_argument("--empty-fiber", type=int,
        help="forbid every internal edge in this difference fiber")
    parser.add_argument("--timeout-ms", type=int, default=300_000)
    parser.add_argument("--random-seed", type=int, default=0)
    parser.add_argument("--dimacs",
        help="write an equisatisfiable bit-blasted DIMACS instance and exit")
    parser.add_argument("--dump-defects", action="store_true",
        help="print repeated target-difference pairs by 2-adic row separation")
    parser.add_argument("--dump-cross-products", action="store_true",
        help="print normalized cross-fiber collision products and q(q-4) violations")
    parser.add_argument("--dump-pair-supports", action="store_true",
        help="print each fixed source pair's precise common-target support")
    parser.add_argument("--dump-relative-completions", action="store_true",
        help="audit cycle types of the four two-hole permutation completions")
    parser.add_argument("--dump-triangle-reversal", action="store_true",
        help="print colored triangle-trace asymmetry under block reversal")
    parser.add_argument("--impose-triangle-reversal", action="store_true",
        help="drop edge reciprocity but impose every colored triangle-trace reversal")
    parser.add_argument("--impose-four-cycle-reversal", action="store_true",
        help="drop edge reciprocity but impose every colored four-cycle trace reversal")
    parser.add_argument("--trace-reversal-core", action="store_true",
        help="impose degree-3/4 trace reversal and print a tracked UNSAT core")
    parser.add_argument("--trace-reversal-group-core", action="store_true",
        help="greedily shrink degree/start-fibre trace-reversal groups")
    parser.add_argument("--directed", action="store_true",
        help="drop reciprocity and give every directed route its own variable")
    parser.add_argument("--reciprocity-core", action="store_true",
        help="use directed variables and print an UNSAT core grouped by fibre pair")
    args = parser.parse_args()

    if args.directed and (args.reciprocity_core or
                          args.impose_triangle_reversal or
                          args.impose_four_cycle_reversal or
                          args.trace_reversal_core or
                          args.trace_reversal_group_core):
        parser.error("--directed cannot be combined with a directed constraint mode")
    if args.reciprocity_core and (args.impose_triangle_reversal or
                                  args.impose_four_cycle_reversal or
                                  args.trace_reversal_core or
                                  args.trace_reversal_group_core):
        parser.error("--reciprocity-core cannot be combined with trace reversal")
    if args.trace_reversal_core and (args.impose_triangle_reversal or
                                     args.impose_four_cycle_reversal):
        parser.error("--trace-reversal-core already imposes both trace families")
    if args.trace_reversal_group_core and (args.impose_triangle_reversal or
                                           args.impose_four_cycle_reversal or
                                           args.trace_reversal_core):
        parser.error("--trace-reversal-group-core is a standalone trace mode")
    if args.reciprocity_core and args.dimacs is not None:
        parser.error("--reciprocity-core cannot be combined with --dimacs")

    q = args.q
    holes = {args.a % q, (-1 - args.a) % q}
    differences = [t for t in range(q) if t not in holes]
    variables: dict[tuple[int, int, int], z3.BoolRef] = {}

    def edge_key(t: int, u: int, r: int) -> tuple[int, int, int]:
        forward = (t, u, r % q)
        if (args.directed or args.reciprocity_core or
                args.impose_triangle_reversal or
                args.impose_four_cycle_reversal or
                args.trace_reversal_core or
                args.trace_reversal_group_core):
            return forward
        reverse = (u, t, (-r) % q)
        return min(forward, reverse)

    def edge(t: int, u: int, r: int) -> z3.BoolRef:
        key = edge_key(t, u, r)
        if key not in variables:
            variables[key] = z3.Bool(f"e_{key[0]}_{key[1]}_{key[2]}")
        return variables[key]

    solver = z3.Solver()
    reciprocity_assumptions: list[z3.BoolRef] = []
    trace_group_assumptions: dict[tuple[str, int], z3.BoolRef] = {}

    if args.trace_reversal_group_core:
        for degree in ("tri", "quad"):
            for t in differences:
                trace_group_assumptions[degree, t] = z3.Bool(
                    f"{degree}_start_{t}")

    if args.reciprocity_core:
        # Track reciprocity by unordered fibre pair.  All non-reciprocity
        # constraints remain hard, so an UNSAT core identifies which block
        # transpose relations participate in the contradiction.
        for i, t in enumerate(differences):
            for u in differences[i:]:
                equations = [
                    edge(t, u, r) == edge(u, t, -r)
                    for r in range(q)
                ]
                label = z3.Bool(f"recip_{t}_{u}")
                reciprocity_assumptions.append(label)
                solver.add(z3.Implies(label, z3.And(equations)))

    # Looplessness.
    for t in differences:
        solver.add(z3.Not(edge(t, t, 0)))

    # Exact target-row hits.  A route with base displacement r lands in row
    # x+r; rows x+t and x+t+1 are the two holes for source difference t.
    for t in differences:
        for r in range(q):
            wanted = 0 if r in {t, (t + 1) % q} else 1
            solver.add(z3.PbEq([(edge(t, u, r), 1) for u in differences],
                               wanted))

    # Exact target-column hits.  For target column displacement c and target
    # difference u, the target base displacement is r=c-u.
    for t in differences:
        for c in range(q):
            wanted = 0 if c in {0, q - 1} else 1
            solver.add(z3.PbEq([
                (edge(t, u, c - u), 1) for u in differences], wanted))

    for specification in args.cap:
        try:
            raw_t, raw_d = map(int, specification.split(":"))
        except ValueError:
            parser.error("--cap must have form DIFFERENCE:SEPARATION")
        t, d = raw_t % q, raw_d % q
        if t not in differences:
            parser.error(f"cap fiber {t} is forbidden by the two holes")
        # Translation invariance makes the common-neighbor count independent
        # of the source base x.
        solver.add(z3.PbLe([
            (z3.And(edge(t, u, r), edge(t, u, r - d)), 1)
            for u in differences for r in range(q)], 1))

    if args.empty_fiber is not None:
        t = args.empty_fiber % q
        if t not in differences:
            parser.error(f"empty fiber {t} is forbidden by the two holes")
        for r in range(q):
            solver.add(z3.Not(edge(t, t, r)))

    if (args.impose_triangle_reversal or args.trace_reversal_core or
            args.trace_reversal_group_core):
        # Reciprocity A_tu=A_ut^T implies equality between every colored
        # triangle trace and its reversed color word.  Retain only these
        # necessary cubic consequences, using otherwise directed blocks.
        def triangle_terms(t: int, u: int, v: int) -> list[z3.BoolRef]:
            return [
                z3.And(edge(t, u, r), edge(u, v, s),
                       edge(v, t, -r - s))
                for r in range(q) for s in range(q)
            ]

        for t in differences:
            for i, u in enumerate(differences):
                for v in differences[i + 1:]:
                    forward = triangle_terms(t, u, v)
                    reverse = triangle_terms(t, v, u)
                    constraint = z3.PbEq(
                        [(term, 1) for term in forward] +
                        [(term, -1) for term in reverse], 0)
                    if args.trace_reversal_core:
                        solver.assert_and_track(
                            constraint, z3.Bool(f"tri_{t}_{u}_{v}"))
                    elif args.trace_reversal_group_core:
                        solver.add(z3.Implies(
                            trace_group_assumptions["tri", t], constraint))
                    else:
                        solver.add(constraint)

    if (args.impose_four_cycle_reversal or args.trace_reversal_core or
            args.trace_reversal_group_core):
        # The analogous necessary consequence for a closed color word
        # t,u,v,w,t.  This retains all four block colors but is still much
        # weaker than entrywise transpose reciprocity.
        def four_cycle_terms(
                t: int, u: int, v: int, w: int) -> list[z3.BoolRef]:
            return [
                z3.And(edge(t, u, r), edge(u, v, s), edge(v, w, h),
                       edge(w, t, -r - s - h))
                for r in range(q) for s in range(q) for h in range(q)
            ]

        for t in differences:
            for i, u in enumerate(differences):
                for w in differences[i + 1:]:
                    for v in differences:
                        forward = four_cycle_terms(t, u, v, w)
                        reverse = four_cycle_terms(t, w, v, u)
                        constraint = z3.PbEq(
                            [(term, 1) for term in forward] +
                            [(term, -1) for term in reverse], 0)
                        if args.trace_reversal_core:
                            solver.assert_and_track(
                                constraint, z3.Bool(f"quad_{t}_{u}_{v}_{w}"))
                        elif args.trace_reversal_group_core:
                            solver.add(z3.Implies(
                                trace_group_assumptions["quad", t], constraint))
                        else:
                            solver.add(constraint)

    if args.dimacs is not None:
        goal = z3.Goal()
        goal.add(*solver.assertions())
        transformed = z3.Then(
            "simplify", "card2bv", "bit-blast", "tseitin-cnf")(goal)
        if len(transformed) != 1:
            raise RuntimeError("CNF conversion unexpectedly produced subgoals")
        cnf_solver = z3.Solver()
        cnf_solver.add(*transformed[0])
        with open(args.dimacs, "w", encoding="ascii") as output:
            output.write(cnf_solver.dimacs())
        print(f"q={q} a={args.a % q} orbit_variables={len(variables)}: "
              f"wrote {args.dimacs}")
        return

    solver.set(timeout=args.timeout_ms, random_seed=args.random_seed)
    active_assumptions = (reciprocity_assumptions or
                          list(trace_group_assumptions.values()))
    result = solver.check(*active_assumptions)
    print(f"q={q} a={args.a % q} orbit_variables={len(variables)}: {result}")

    if result == z3.unsat and args.reciprocity_core:
        core = list(solver.unsat_core())
        # Greedily shrink the sufficient set.  This need not find a
        # cardinality-minimum core, but every retained block is necessary
        # relative to the final deletion order.
        for label in list(core):
            candidate = [other for other in core if not z3.eq(other, label)]
            if solver.check(*candidate) == z3.unsat:
                core = candidate
        solver.check(*core)
        print("  reciprocity_core=" + str(sorted(str(label) for label in core)))
    if result == z3.unsat and args.trace_reversal_core:
        core = sorted(str(label) for label in solver.unsat_core())
        print("  trace_reversal_core=" + str(core))
    if result == z3.unsat and args.trace_reversal_group_core:
        core = list(solver.unsat_core())
        for label in list(core):
            candidate = [other for other in core if not z3.eq(other, label)]
            if solver.check(*candidate) == z3.unsat:
                core = candidate
        solver.check(*core)
        print("  trace_reversal_group_core=" +
              str(sorted(str(label) for label in core)))

    if result == z3.sat:
        model = solver.model()
        for t in differences:
            internal_steps = [r for r in range(1, q)
                if z3.is_true(model.eval(edge(t, t, r)))]
            if internal_steps:
                print(f"  fiber {t}: internal_steps={internal_steps}")
        if args.dump_defects:
            level_totals: Counter[int] = Counter()
            for t in differences:
                rows_by_target: dict[int, list[int]] = defaultdict(list)
                for r in range(q):
                    for u in differences:
                        if z3.is_true(model.eval(edge(t, u, r))):
                            rows_by_target[u].append(r)
                levels: Counter[int] = Counter()
                repeated_targets = 0
                excess = 0
                for rows in rows_by_target.values():
                    if len(rows) < 2:
                        continue
                    repeated_targets += 1
                    excess += len(rows) - 1
                    for i, r in enumerate(rows):
                        for s in rows[i + 1:]:
                            separation = (s - r) % q
                            level = (separation & -separation).bit_length() - 1
                            levels[level] += 1
                            level_totals[level] += 1
                print(f"  fiber {t}: repeated_targets={repeated_targets} "
                      f"excess={excess} defect_levels={dict(sorted(levels.items()))}")
            print(f"  all defect_levels={dict(sorted(level_totals.items()))}")
        if args.dump_cross_products:
            # In a translation-invariant model, the matching-orbit
            # multiplicity at a precise target cell (y,u) is the number of
            # selected displacements r from source fiber t to target fiber u.
            # Hence the full cross-fiber collision sum is q times this dot
            # product.  The sufficient Lean terminal asks for the normalized
            # dot product to be at most q-4 for every distinct pair.
            multiplicities = {
                t: {
                    u: sum(z3.is_true(model.eval(edge(t, u, r)))
                           for r in range(q))
                    for u in differences
                }
                for t in differences
            }
            violations = []
            maximum = (0, None)
            for i, t in enumerate(differences):
                for v in differences[i + 1:]:
                    product = sum(multiplicities[t][u] * multiplicities[v][u]
                                  for u in differences)
                    if product > maximum[0]:
                        maximum = (product, (t, v))
                    if product > q - 4:
                        violations.append((t, v, product))
            print(f"  cross_product_bound={q - 4} maximum={maximum[0]} "
                  f"at={maximum[1]} violations={violations}")
        if args.dump_pair_supports:
            # Translation invariance normalizes the first source base to 0.
            # For the pair of source cells (0,t) and (d,t), a common target
            # cell has absolute coordinates (r,r+u): the first route uses
            # displacement r and the second uses displacement r-d.
            supports = []
            level_counts: Counter[int] = Counter()
            for t in differences:
                for d in range(1, q):
                    support = [
                        (u, r)
                        for u in differences for r in range(q)
                        if z3.is_true(model.eval(edge(t, u, r)))
                        and z3.is_true(model.eval(edge(t, u, r - d)))
                    ]
                    if not support:
                        continue
                    level = (d & -d).bit_length() - 1
                    level_counts[level] += len(support)
                    supports.append((len(support), t, d, level, support))
            supports.sort(key=lambda item: (-item[0], item[1], item[2]))
            print(f"  pair_support_level_mass={dict(sorted(level_counts.items()))} "
                  f"nonempty_pairs={len(supports)}")
            for size, t, d, level, support in supports:
                print(f"  pair fiber={t} shift={d} v2={level} "
                      f"count={size} targets={support}")
        if args.dump_relative_completions:
            # A source cell (x,x+t) routes every target row except
            # x+t,x+t+1 to exactly one target column except x,x-1.  Complete
            # this partial bijection in the two possible ways.  Fixed points
            # of Q_d^{-1} Q_0 are common target cells of the two completed
            # routes; those outside either hole pair are genuine supports.
            def completion(t: int, x: int, crossed: bool) -> list[int]:
                route = [-1] * q
                for y in range(q):
                    r = (y - x) % q
                    if r in {t, (t + 1) % q}:
                        continue
                    hits = [u for u in differences
                            if z3.is_true(model.eval(edge(t, u, r)))]
                    if len(hits) != 1:
                        raise RuntimeError("row-hit law missing in model")
                    route[y] = (x + r + hits[0]) % q
                source_holes = [(x + t) % q, (x + t + 1) % q]
                target_holes = [(x - 1) % q, x % q]
                if crossed:
                    target_holes.reverse()
                for y, c in zip(source_holes, target_holes):
                    route[y] = c
                if sorted(route) != list(range(q)):
                    raise RuntimeError("column-hit law missing in completion")
                return route

            def relative_cycles(left: list[int], right: list[int]) -> list[list[int]]:
                inverse_right = [0] * q
                for y, c in enumerate(right):
                    inverse_right[c] = y
                permutation = [inverse_right[left[y]] for y in range(q)]
                seen: set[int] = set()
                cycles: list[list[int]] = []
                for start in range(q):
                    if start in seen:
                        continue
                    cycle = []
                    y = start
                    while y not in seen:
                        seen.add(y)
                        cycle.append(y)
                        y = permutation[y]
                    cycles.append(cycle)
                return cycles

            completion_rows = []
            for t in differences:
                base = [completion(t, 0, crossed) for crossed in (False, True)]
                for d in range(1, q):
                    shifted = [completion(t, d, crossed)
                               for crossed in (False, True)]
                    genuine_rows = set(range(q)) - {
                        t % q, (t + 1) % q,
                        (d + t) % q, (d + t + 1) % q,
                    }
                    genuine = sum(base[0][y] == shifted[0][y]
                                  for y in genuine_rows)
                    types = []
                    fixed = []
                    signs = []
                    for left in base:
                        for right in shifted:
                            cycles = relative_cycles(left, right)
                            types.append(tuple(sorted(map(len, cycles))))
                            fixed.append(sum(len(cycle) == 1 for cycle in cycles))
                            signs.append((q - len(cycles)) % 2)
                    completion_rows.append((genuine, t, d, types, fixed, signs))
            completion_rows.sort(key=lambda item: (-item[0], item[1], item[2]))
            for genuine, t, d, types, fixed, signs in completion_rows:
                if genuine >= 1:
                    print(f"  relative fiber={t} shift={d} genuine={genuine} "
                          f"fixed={fixed} signs={signs} cycle_types={types}")
        if args.dump_triangle_reversal:
            # With A_tu[x,y] = E(t,u,y-x), the normalized colored triangle
            # trace tr(A_tu A_uv A_vt)/q is the cyclic convolution below.
            # Block-transpose reciprocity forces T(t,u,v)=T(t,v,u).  A
            # directed model need not satisfy this, so the nonzero entries
            # identify genuinely reciprocity-sensitive colored words.
            selected = {
                (t, u, r): z3.is_true(model.eval(edge(t, u, r)))
                for t in differences for u in differences for r in range(q)
            }

            def triangle_trace(t: int, u: int, v: int) -> int:
                return sum(
                    selected[t, u, r]
                    and selected[u, v, s]
                    and selected[v, t, (-r - s) % q]
                    for r in range(q) for s in range(q)
                )

            asymmetries = []
            for t in differences:
                for i, u in enumerate(differences):
                    for v in differences[i + 1:]:
                        forward = triangle_trace(t, u, v)
                        reverse = triangle_trace(t, v, u)
                        if forward != reverse:
                            asymmetries.append(
                                (abs(forward - reverse), t, u, v,
                                 forward, reverse))
            asymmetries.sort(reverse=True)
            print(f"  triangle_reversal_asymmetries={len(asymmetries)}")
            for _, t, u, v, forward, reverse in asymmetries:
                print(f"  triangle t={t} u={u} v={v} "
                      f"forward={forward} reverse={reverse}")


if __name__ == "__main__":
    main()
