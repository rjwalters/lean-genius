#!/usr/bin/env python3
"""Faithful q=4 falsifier search for inverse-potential sign condition (P8).

The model is an actual symmetric loopless 4-regular C4-free adjacency
matrix A on 16 vertices, not merely a Laplacian abstraction.  Vertex 0 has
neighborhood {1,2,3,4}.  We require an exact rational solution of

    A x = e_0

and ask whether either an off-diagonal nonsource has positive potential or
the root has positive potential while deg_T(0)>0.  Either outcome refutes
the corresponding horn of root-aware (P8) at q=4.  SAT output includes the
full graph and exact rational potential for independent verification.
"""

import argparse
from collections import Counter

import sympy
from z3 import And, Bool, If, Or, Real, Solver, Sum, is_true, sat


Q = 4
N = Q * Q
ROOT = 0
SOURCE = set(range(1, Q + 1))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root-triangles", type=int, choices=range(Q // 2 + 1))
    parser.add_argument("--timeout-ms", type=int, default=300_000)
    parser.add_argument("--any-column", action="store_true",
                        help="seek any exact Ax=e_0 column, without a sign violation")
    parser.add_argument("--graph-only", action="store_true",
                        help="seek only the finite incidence graph")
    parser.add_argument("--connected-defect", action="store_true",
                        help="require the second-order defect graph to be connected")
    parser.add_argument("--enumerate", type=int, default=0,
                        help="enumerate this many graph models, stopping at a nonsingular one")
    args = parser.parse_args()
    graph_only = args.graph_only or bool(args.enumerate)

    solver = Solver()
    solver.set(timeout=args.timeout_ms)

    edge_var = {
        (i, j): Bool(f"a_{i}_{j}")
        for i in range(N) for j in range(i + 1, N)
    }

    def edge(i: int, j: int):
        if i == j:
            return False
        return edge_var[tuple(sorted((i, j)))]

    # Root-neighborhood symmetry breaking and exact regularity.
    for j in range(1, N):
        solver.add(edge(ROOT, j) == (j in SOURCE))
    if args.root_triangles is not None:
        canonical_source_edges = {
            (2 * index + 1, 2 * index + 2)
            for index in range(args.root_triangles)
        }
        for i in SOURCE:
            for j in SOURCE:
                if i < j:
                    solver.add(edge(i, j) == ((i, j) in canonical_source_edges))
    for i in range(N):
        solver.add(Sum([If(edge(i, j), 1, 0) for j in range(N) if j != i]) == Q)

    # C4-free is exactly the pairwise common-neighbor cap one.
    common = {}
    for i in range(N):
        for j in range(i + 1, N):
            count = Sum([
                If(And(edge(i, z), edge(j, z)), 1, 0)
                for z in range(N) if z != i and z != j
            ])
            common[(i, j)] = count
            solver.add(count <= 1)

    if args.connected_defect:
        # Exact bounded reachability in the defect graph.  A pair is a
        # defect edge precisely when its common-neighbor count is zero.
        reachable = [
            [Bool(f"reach_{step}_{vertex}") for vertex in range(N)]
            for step in range(N)
        ]
        for vertex in range(N):
            solver.add(reachable[0][vertex] == (vertex == ROOT))
        for step in range(1, N):
            for vertex in range(N):
                arrivals = [
                    And(reachable[step - 1][other],
                        common[tuple(sorted((vertex, other)))] == 0)
                    for other in range(N) if other != vertex
                ]
                solver.add(
                    reachable[step][vertex]
                    == Or(reachable[step - 1][vertex], *arrivals)
                )
        solver.add(And(reachable[-1]))

    potential = [Real(f"x_{i}") for i in range(N)]
    if not graph_only:
        for i in range(N):
            solver.add(
                Sum([If(edge(i, j), potential[j], 0) for j in range(N) if j != i])
                == (1 if i == ROOT else 0)
            )

        positive_off_diagonal_sink = Or([
            potential[v] > 0 for v in range(Q + 1, N)
        ])
        root_has_triangle_free_edge = Or([
            common[tuple(sorted((ROOT, u)))] == 0 for u in SOURCE
        ])
        adverse_root_term = And(potential[ROOT] > 0, root_has_triangle_free_edge)
        if not args.any_column:
            solver.add(Or(positive_off_diagonal_sink, adverse_root_term))

    if args.enumerate:
        rank_histogram: Counter[int] = Counter()
        for index in range(args.enumerate):
            result = solver.check()
            if result != sat:
                print("enumeration stopped:", result, "after", index, "models")
                return
            model = solver.model()
            edges = [
                pair for pair, variable in edge_var.items()
                if is_true(model.eval(variable))
            ]
            matrix = sympy.zeros(N)
            for i, j in edges:
                matrix[i, j] = matrix[j, i] = 1
            rank = matrix.rank()
            rank_histogram[rank] += 1
            if rank == N:
                inverse_column = matrix.inv()[:, ROOT]
                print("nonsingular model", index)
                print("edges =", edges)
                print("x =", list(inverse_column))
                return
            solver.add(Or([
                variable != model.eval(variable)
                for variable in edge_var.values()
            ]))
            if index % 100 == 99:
                print("enumerated", index + 1, "models; all singular")
        print("bounded enumeration complete:", args.enumerate, "models; all singular")
        print("rank histogram:", dict(sorted(rank_histogram.items())))
        return

    result = solver.check()
    print("result:", result)
    if result != sat:
        return

    model = solver.model()
    edges = [pair for pair, variable in edge_var.items() if is_true(model.eval(variable))]
    values = [model.eval(value, model_completion=True) for value in potential]
    positive_sinks = [] if graph_only else [
        v for v in range(Q + 1, N)
        if is_true(model.eval(potential[v] > 0))
    ]
    root_t_neighbors = [
        u for u in SOURCE
        if model.eval(common[tuple(sorted((ROOT, u)))], model_completion=True).as_long() == 0
    ]

    print("edges =", edges)
    if not graph_only:
        print("x =", values)
    print("positive off-diagonal sinks =", positive_sinks)
    print("root T-neighbors =", root_t_neighbors)
    if not graph_only:
        print("adverse root term =", bool(root_t_neighbors) and is_true(model.eval(potential[0] > 0)))


if __name__ == "__main__":
    main()
