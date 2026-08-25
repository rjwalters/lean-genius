#!/usr/bin/env python3
"""Search exact q^2-vertex incidence controls for inverse-potential P8.

The finite layer is a symmetric loopless q-regular C4-free graph.  Vertex
zero has the canonical neighborhood 1,...,q and a canonical matching of a
prescribed size inside that neighborhood.  Models are blocked one at a time;
for every nonsingular adjacency matrix we compute A^{-1}e_0 over Q and test
the root-aware sign condition from NONBIP_CONNECTED_INVERSE_POTENTIAL_AUDIT.

This is a bounded falsifier, not an exhaustive isomorph-free classifier.
"""

import argparse
from collections import Counter

import sympy
from z3 import And, Bool, If, Or, Solver, Sum, is_true, sat


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--q", type=int, required=True)
    parser.add_argument("--root-triangles", type=int, required=True)
    parser.add_argument("--enumerate", type=int, default=1000)
    parser.add_argument("--timeout-ms", type=int, default=300_000)
    args = parser.parse_args()

    q = args.q
    n = q * q
    root = 0
    source = set(range(1, q + 1))
    if q < 2 or not 0 <= args.root_triangles <= q // 2:
        parser.error("require q >= 2 and 0 <= root-triangles <= floor(q/2)")
    if n * q % 2:
        print("unsat: the degree sum q^3 is odd")
        return
    if args.root_triangles == 0:
        # The root, its q neighbors, and their q-1 other neighbors are all
        # distinct in a C4-free graph, already requiring q^2+1 vertices.
        print("unsat: the root radius-two Moore count needs q^2+1 vertices")
        return

    solver = Solver()
    solver.set(timeout=args.timeout_ms)
    edge_var = {
        (i, j): Bool(f"a_{i}_{j}")
        for i in range(n) for j in range(i + 1, n)
    }

    def edge(i: int, j: int):
        if i == j:
            return False
        return edge_var[tuple(sorted((i, j)))]

    for j in range(1, n):
        solver.add(edge(root, j) == (j in source))
    canonical_source_edges = {
        (2 * index + 1, 2 * index + 2)
        for index in range(args.root_triangles)
    }
    for i in source:
        for j in source:
            if i < j:
                solver.add(edge(i, j) == ((i, j) in canonical_source_edges))
    for i in range(n):
        solver.add(Sum([
            If(edge(i, j), 1, 0) for j in range(n) if j != i
        ]) == q)
    for i in range(n):
        for j in range(i + 1, n):
            solver.add(Sum([
                If(And(edge(i, z), edge(j, z)), 1, 0)
                for z in range(n) if z != i and z != j
            ]) <= 1)

    rank_histogram: Counter[int] = Counter()
    nonsingular = 0
    for index in range(args.enumerate):
        result = solver.check()
        if result != sat:
            print("enumeration stopped:", result, "after", index, "models")
            break
        model = solver.model()
        edges = [
            pair for pair, variable in edge_var.items()
            if is_true(model.eval(variable))
        ]
        matrix = sympy.zeros(n)
        for i, j in edges:
            matrix[i, j] = matrix[j, i] = 1
        rank = matrix.rank()
        rank_histogram[rank] += 1
        if rank == n:
            nonsingular += 1
            x = matrix.inv()[:, root]
            sinks = range(q + 1, n)
            positive_sinks = [v for v in sinks if x[v] > 0]
            root_degree_t = sum(
                1 for u in source
                if sum(1 for z in range(n) if matrix[root, z] and matrix[u, z]) == 0
            )
            p8 = not positive_sinks and root_degree_t * x[root] <= 0
            print("nonsingular model", index, "P8", p8)
            print("rank =", rank, "root_degree_T =", root_degree_t)
            print("positive sinks =", positive_sinks)
            print("x_root =", x[root], "x =", list(x))
            print("edges =", edges)
            if not p8:
                print("P8 COUNTERMODEL")
                return
        solver.add(Or([
            variable != model.eval(variable) for variable in edge_var.values()
        ]))
        if index % 100 == 99:
            print("enumerated", index + 1, "models")

    print("bounded enumeration complete")
    print("nonsingular models:", nonsingular)
    print("rank histogram:", dict(sorted(rank_histogram.items())))


if __name__ == "__main__":
    main()
