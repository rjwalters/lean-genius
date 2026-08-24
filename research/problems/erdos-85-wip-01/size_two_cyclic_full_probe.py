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
    parser.add_argument("--uniform-fibre-loads", action="store_true",
        help="require every target to have exactly one neighbour in each source fibre")
    parser.add_argument("--minimal-block-variance", "--sharp-fibre-loads",
        dest="minimal_block_variance", action="store_true",
        help="give each source one zero, one double, and otherwise one target per fibre")
    parser.add_argument("--dump-fibre-loads", action="store_true",
        help="on SAT, print target-fibre degree profiles for every source")
    parser.add_argument("--directed", action="store_true",
        help="drop reciprocity and use one variable per ordered pair")
    parser.add_argument("--reciprocity-core", action="store_true",
        help="use directed variables and shrink reciprocity by fibre-pair groups")
    parser.add_argument("--joint-group-core", action="store_true",
        help="shrink reciprocity blocks and full-cap families together")
    parser.add_argument("--joint-separation-core", action="store_true",
        help="shrink reciprocity blocks and cap fibre/separation groups")
    parser.add_argument("--dump-internal-profile", action="store_true",
        help="on SAT, print internal edges and occupied bases in each fibre")
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
    parser.add_argument("--timeout-ms", type=int, default=300_000)
    parser.add_argument("--dimacs")
    args = parser.parse_args()

    if sum((args.directed, args.reciprocity_core, args.joint_group_core,
            args.joint_separation_core)) > 1:
        parser.error("directed/core modes are mutually exclusive")
    if (args.reciprocity_core or args.joint_group_core or
            args.joint_separation_core) and args.dimacs is not None:
        parser.error("core modes cannot be combined with --dimacs")
    if args.no_caps and args.only_cap_pair is not None:
        parser.error("--no-caps and --only-cap-pair are incompatible")

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

    solver = z3.Solver()
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
    for source in vertices:
        x, t = source
        for y in range(q):
            wanted = 0 if y in {(x + t) % q, (x + t + 1) % q} else 1
            solver.add(z3.PbEq(
                [(edge(source, (y, u)), 1) for u in differences], wanted))

    # Exact target-column hits.  A cell (y,u) has absolute second coordinate
    # y+u.  Columns x and x-1 are the two component-neighbour holes.
    for source in vertices:
        x, _ = source
        for c in range(q):
            wanted = 0 if c in {x, (x - 1) % q} else 1
            targets = [((c - u) % q, u) for u in differences]
            assert all(target in vertex_set for target in targets)
            solver.add(z3.PbEq(
                [(edge(source, target), 1) for target in targets], wanted))

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
    if args.minimal_block_variance:
        for source in vertices:
            loads = []
            for u in differences:
                load = z3.Int(f"load_{source[0]}_{source[1]}_{u}")
                solver.add(load == z3.Sum([
                    z3.If(edge(source, (y, u)), 1, 0)
                    for y in range(q)
                ]))
                solver.add(load >= 0, load <= 2)
                loads.append(load)
            solver.add(z3.PbEq([(load == 0, 1) for load in loads], 1))
            solver.add(z3.PbEq([(load == 2, 1) for load in loads], 1))

    # Full same-difference cap: any two distinct bases in one fibre have at
    # most one precise common target cell.
    if not args.no_caps:
        for t in differences:
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
        print(f"q={q} vertices={len(vertices)} edge_variables={len(variables)}: "
              f"wrote {args.dimacs}")
        return

    solver.set(timeout=args.timeout_ms)
    active_assumptions = reciprocity_assumptions + list(cap_assumptions.values())
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
    if result == z3.sat and args.dump_fibre_loads:
        model = solver.model()
        for source in vertices:
            loads = [sum(z3.is_true(model.eval(
                edge(source, (y, u)), model_completion=True))
                for y in range(q)) for u in differences]
            print(f"  source={source} loads={dict(zip(differences, loads))}")
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
