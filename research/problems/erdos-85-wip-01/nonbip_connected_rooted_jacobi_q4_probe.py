#!/usr/bin/env python3
"""Probe rooted characteristic/minor residues in the q=4 calibration corpus.

This is a bounded falsifier for the vertex-deleted Jacobi/resolvent proposal
from divergence round 77.  It enumerates regular C4-free graphs on 16 labelled
vertices (with the root neighbourhood fixed), constructs the defect graph D,
and records characteristic-polynomial coefficients of the principal deletions
of A, A+I, A-I, and 4I-D modulo 8 and 16.

The output deliberately separates residues by the rooted triangle degree.  A
useful candidate must be uniform for reasons stronger than a q=4 profile
accident and must occur low enough in the deleted characteristic polynomial to
admit a Jacobi/Sachs derivation.  If no nontrivial low coefficient is uniform,
the proposed route is cut before formalization.
"""

from __future__ import annotations

import argparse
import itertools
from collections import defaultdict

import sympy as sp
from z3 import And, Bool, If, Or, Solver, Sum, is_true, sat


Q = 4
N = Q * Q
ROOT_NEIGHBORS = set(range(1, Q + 1))


def matrix_from_edges(edges: list[tuple[int, int]]) -> sp.Matrix:
    matrix = sp.zeros(N)
    for left, right in edges:
        matrix[left, right] = matrix[right, left] = 1
    return matrix


def defect_matrix(adjacency: sp.Matrix) -> sp.Matrix:
    square = adjacency * adjacency
    return sp.Matrix(
        N,
        N,
        lambda left, right: int(left != right and square[left, right] == 0),
    )


def delete_index(matrix: sp.Matrix, root: int) -> sp.Matrix:
    keep = [index for index in range(N) if index != root]
    return matrix.extract(keep, keep)


def triangle_degree(adjacency: sp.Matrix, root: int) -> int:
    neighbors = [vertex for vertex in range(N) if adjacency[root, vertex] == 1]
    return sum(adjacency[left, right] for left, right in itertools.combinations(neighbors, 2))


def coefficient_residues(
    matrix: sp.Matrix, root: int, width: int, window: str
) -> tuple[int, ...]:
    # charpoly() returns [1, c1, ..., c15].  The head is the relevant window
    # for the Laurent expansion of the rooted resolvent; the tail contains the
    # determinant/minor data.  Keep both available so the probe cannot confuse
    # these two genuinely different Jacobi interfaces.
    coefficients = delete_index(matrix, root).charpoly().all_coeffs()
    selected = coefficients[:width] if window == "head" else coefficients[-width:]
    return tuple(int(value) for value in selected)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--models", type=int, default=32)
    parser.add_argument("--timeout-ms", type=int, default=120_000)
    parser.add_argument("--width", type=int, default=7)
    parser.add_argument("--window", choices=("head", "tail", "both"), default="both")
    args = parser.parse_args()

    solver = Solver()
    solver.set(timeout=args.timeout_ms, random_seed=850077)
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
            Sum([If(edge(vertex, other), 1, 0) for other in range(N) if other != vertex])
            == Q
        )
    for left, right in itertools.combinations(range(N), 2):
        solver.add(
            Sum(
                [
                    If(And(edge(left, middle), edge(right, middle)), 1, 0)
                    for middle in range(N)
                    if middle != left and middle != right
                ]
            )
            <= 1
        )

    names = ("A", "A+I", "A-I", "4I-D")
    windows = ("head", "tail") if args.window == "both" else (args.window,)
    by_profile = {
        (name, window): defaultdict(lambda: [set() for _ in range(args.width)])
        for name in names
        for window in windows
    }
    all_residues = {
        (name, window): [set() for _ in range(args.width)]
        for name in names
        for window in windows
    }

    for model_index in range(args.models):
        result = solver.check()
        if result != sat:
            print(f"enumeration_stopped={result}; models={model_index}")
            raise SystemExit(2)
        model = solver.model()
        edges = [pair for pair, variable in variables.items() if is_true(model.eval(variable))]
        adjacency = matrix_from_edges(edges)
        defect = defect_matrix(adjacency)
        matrices = {
            "A": adjacency,
            "A+I": adjacency + sp.eye(N),
            "A-I": adjacency - sp.eye(N),
            "4I-D": Q * sp.eye(N) - defect,
        }
        for root in range(N):
            profile = triangle_degree(adjacency, root)
            for name, matrix in matrices.items():
                for window in windows:
                    values = coefficient_residues(matrix, root, args.width, window)
                    for offset, value in enumerate(values):
                        by_profile[name, window][profile][offset].add(value % 16)
                        all_residues[name, window][offset].add(value % 16)
        solver.add(Or([variable != model.eval(variable) for variable in variables.values()]))

    print(f"bounded_models={args.models}; roots={args.models * N}; modulus=16")
    print("head offsets start with the monic coefficient; tail offsets end with determinant")
    for name in names:
        for window in windows:
            print(f"matrix={name}; window={window}")
            print(f"  all={list(map(sorted, all_residues[name, window]))}")
            for profile in sorted(by_profile[name, window]):
                print(
                    f"  triangle_degree={profile}: "
                    f"{list(map(sorted, by_profile[name, window][profile]))}"
                )
            constants = [
                (offset, next(iter(values)))
                for offset, values in enumerate(all_residues[name, window])
                if len(values) == 1
            ]
            print(f"  globally_constant_offsets={constants}")


if __name__ == "__main__":
    main()
