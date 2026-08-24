#!/usr/bin/env python3
"""Search two full reciprocal codes joined by a small rank-lowering trade."""

from __future__ import annotations

import argparse
from itertools import combinations

import z3


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("q", type=int)
    parser.add_argument("support", type=int)
    parser.add_argument("--a", type=int, required=True)
    parser.add_argument("--caps", action="store_true",
                        help="impose every same-fibre cap in both codes")
    parser.add_argument("--cap-fibres", type=int, nargs="+",
                        help="impose caps only in the listed endpoint fibres")
    parser.add_argument("--max-old-rank", type=int,
                        help="upper-bound the defect rank of the first code")
    parser.add_argument("--timeout-ms", type=int, default=300_000)
    args = parser.parse_args()
    q = args.q
    holes = {args.a % q, (-1 - args.a) % q}
    differences = tuple(t for t in range(q) if t not in holes)
    vertices = tuple((x, t) for x in range(q) for t in differences)
    index = {vertex: i for i, vertex in enumerate(vertices)}

    solver = z3.Solver()
    solver.set(timeout=args.timeout_ms)
    edge_vars: list[dict[tuple[int, int], z3.BoolRef]] = []
    zero_totals = []

    for code in range(2):
        edges = {
            (i, j): z3.Bool(f"e_{code}_{i}_{j}")
            for i, j in combinations(range(len(vertices)), 2)
        }
        edge_vars.append(edges)

        def edge(left: tuple[int, int], right: tuple[int, int]) -> z3.BoolRef:
            i, j = index[left], index[right]
            if i == j:
                return z3.BoolVal(False)
            return edges[min(i, j), max(i, j)]

        # Both exact punctured projections.
        for source in vertices:
            x, t = source
            for y in range(q):
                wanted = 0 if y in {(x + t) % q, (x + t + 1) % q} else 1
                solver.add(z3.PbEq([
                    (edge(source, (y, u)), 1) for u in differences
                ], wanted))
            for column in range(q):
                wanted = 0 if column in {x, (x - 1) % q} else 1
                solver.add(z3.PbEq([
                    (edge(source, ((column - u) % q, u)), 1)
                    for u in differences
                ], wanted))

        if args.caps or args.cap_fibres is not None:
            capped = (set(differences) if args.caps else
                      {value % q for value in args.cap_fibres})
            for t in differences:
                if t not in capped:
                    continue
                for x, z in combinations(range(q), 2):
                    solver.add(z3.PbLe([
                        (z3.And(edge((x, t), target),
                                edge((z, t), target)), 1)
                        for target in vertices
                    ], 1))

        zeros = []
        for source in vertices:
            for u in differences:
                load = z3.Sum([
                    z3.If(edge(source, (y, u)), 1, 0) for y in range(q)
                ])
                zeros.append(z3.If(load == 0, 1, 0))
        zero_totals.append(z3.Sum(zeros))

    # The two undirected graphs differ only inside the selected support, and
    # every selected vertex is genuinely incident with a changed edge.
    selected = [z3.Bool(f"selected_{i}") for i in range(len(vertices))]
    incident_changes: list[list[z3.BoolRef]] = [
        [] for _ in range(len(vertices))]
    for i, j in combinations(range(len(vertices)), 2):
        changed = z3.Xor(edge_vars[0][i, j], edge_vars[1][i, j])
        solver.add(z3.Implies(changed, z3.And(selected[i], selected[j])))
        incident_changes[i].append(changed)
        incident_changes[j].append(changed)
    for i in range(len(vertices)):
        solver.add(selected[i] == z3.Or(incident_changes[i]))
    solver.add(z3.PbEq([(value, 1) for value in selected], args.support))
    solver.add(zero_totals[1] < zero_totals[0])
    if args.max_old_rank is not None:
        solver.add(zero_totals[0] <= args.max_old_rank)

    result = solver.check()
    cap_scope = ("all" if args.caps else
                 sorted({value % q for value in args.cap_fibres})
                 if args.cap_fibres is not None else "none")
    print(f"q={q} a={args.a % q} support={args.support} "
          f"cap_fibres={cap_scope}: {result}")
    if result != z3.sat:
        return
    model = solver.model()
    support = [vertices[i] for i, value in enumerate(selected)
               if z3.is_true(model.eval(value))]
    changed_edges = [
        (vertices[i], vertices[j])
        for i, j in combinations(range(len(vertices)), 2)
        if z3.is_true(model.eval(
            z3.Xor(edge_vars[0][i, j], edge_vars[1][i, j])))
    ]
    print(f"  defect_rank={model.eval(zero_totals[0])} -> "
          f"{model.eval(zero_totals[1])}")
    print(f"  support={support}")
    print(f"  changed_edges={changed_edges}")


if __name__ == "__main__":
    main()
