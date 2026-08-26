#!/usr/bin/env python3
"""Bounded q=4 falsifier for the affine triangle-degree Schur potential."""

from __future__ import annotations

import argparse
import itertools
from collections import Counter

import sympy
from z3 import And, Bool, If, Or, Solver, Sum, is_true, sat


Q = 4
N = Q * Q
ROOT_NEIGHBORS = set(range(1, Q + 1))


def affine_profile(edges: list[tuple[int, int]]) -> tuple[tuple[int, ...], tuple[int, ...]]:
    adjacency = sympy.zeros(N)
    for left, right in edges:
        adjacency[left, right] = adjacency[right, left] = 1

    triangles = [
        triple
        for triple in itertools.combinations(range(N), 3)
        if all(adjacency[left, right] for left, right in itertools.combinations(triple, 2))
    ]
    incidence = sympy.zeros(N, len(triangles))
    triangle_degrees = [0] * N
    for column, triple in enumerate(triangles):
        for vertex in triple:
            incidence[vertex, column] = 1
            triangle_degrees[vertex] += 1

    remainder = adjacency.copy()
    for triple in triangles:
        for left, right in itertools.combinations(triple, 2):
            remainder[left, right] = remainder[right, left] = 0
    core = remainder - sympy.diag(*triangle_degrees)
    assert adjacency == core + incidence * incidence.T

    # T1: Kt = t^2 - (q+1)t + (q^2+2)/3.
    t = sympy.Matrix(triangle_degrees)
    kt = remainder * t
    t1_residual = tuple(
        int(kt[vertex] - (t[vertex] ** 2 - (Q + 1) * t[vertex] + (Q * Q + 2) // 3))
        for vertex in range(N)
    )
    # T2: every A-triangle has triangle-degree mass q+1.
    t2_residual = tuple(sum(triangle_degrees[vertex] for vertex in triple) - (Q + 1) for triple in triangles)

    # When T1/T2 hold, z=(q+1-3t)/(q-2) is a denominator-free
    # certificate after scaling: Mz=1 and H^Tz=0.
    z = sympy.Matrix([(Q + 1 - 3 * value) / sympy.Integer(Q - 2) for value in triangle_degrees])
    assert core * z == sympy.ones(N, 1) if not any(t1_residual) else True
    assert incidence.T * z == sympy.zeros(len(triangles), 1) if not any(t2_residual) else True
    if not any(t1_residual) and not any(t2_residual):
        kernel = (sympy.ones(N, 1) - Q * z) / 3
        assert adjacency * kernel == sympy.zeros(N, 1)
        assert kernel != sympy.zeros(N, 1)

    return t1_residual, t2_residual


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--models", type=int, default=256)
    parser.add_argument("--timeout-ms", type=int, default=120_000)
    args = parser.parse_args()

    solver = Solver()
    solver.set(timeout=args.timeout_ms, random_seed=850074)
    variables = {
        (left, right): Bool(f"a_{left}_{right}")
        for left in range(N)
        for right in range(left + 1, N)
    }

    def edge(left: int, right: int):
        if left == right:
            return False
        return variables[tuple(sorted((left, right)))]

    for vertex in range(1, N):
        solver.add(edge(0, vertex) == (vertex in ROOT_NEIGHBORS))
    for vertex in range(N):
        solver.add(
            Sum([If(edge(vertex, other), 1, 0) for other in range(N) if other != vertex]) == Q
        )
    for left, right in itertools.combinations(range(N), 2):
        solver.add(
            Sum(
                [
                    If(And(edge(left, common), edge(right, common)), 1, 0)
                    for common in range(N)
                    if common != left and common != right
                ]
            )
            <= 1
        )

    triangle_counts: Counter[int] = Counter()
    for index in range(args.models):
        result = solver.check()
        if result != sat:
            print(f"enumeration_stopped={result}; models={index}")
            raise SystemExit(2)
        model = solver.model()
        edges = [pair for pair, variable in variables.items() if is_true(model.eval(variable))]
        t1_residual, t2_residual = affine_profile(edges)
        triangle_counts[len(t2_residual)] += 1
        if any(t1_residual) or any(t2_residual):
            print(
                f"falsifier_model={index}; t1_residual={t1_residual}; "
                f"t2_residual={t2_residual}; edges={edges}"
            )
            raise SystemExit(1)
        solver.add(Or([variable != model.eval(variable) for variable in variables.values()]))

    print(f"bounded_models={args.models}")
    print(f"triangle_counts={dict(sorted(triangle_counts.items()))}")
    print("T1_universal_on_sample=true")
    print("T2_universal_on_sample=true")
    print("affine_certificate_universal_on_sample=true")


if __name__ == "__main__":
    main()
