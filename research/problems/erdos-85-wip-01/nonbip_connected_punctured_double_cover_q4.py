#!/usr/bin/env python3
"""Punctured bipartite-double-cover matching probe for q=4.

Deleting both lifts of a root x from the bipartite double cover of A leaves a
bipartite graph with biadjacency matrix A with row and column x deleted.  Its
perfect-matching count is therefore permanent(A_xhat).  This bounded probe
computes that count modulo 8 and groups it by rooted triangle degree.  The
rooted Sachs target is uniform on this corpus, so variation cuts any proposal
that tries to identify it with this raw matching/Arf residue.
"""

from __future__ import annotations

import argparse
import itertools
from collections import defaultdict

from z3 import And, Bool, If, Or, Solver, Sum, is_true, sat


Q = 4
N = Q * Q
ROOT_NEIGHBORS = set(range(1, Q + 1))


def permanent_mod(rows: list[int], width: int, modulus: int) -> int:
    """Subset DP permanent for a 0/1 matrix, reduced throughout."""
    dp = [0] * (1 << width)
    dp[0] = 1
    for row_index, allowed in enumerate(rows):
        next_dp = [0] * (1 << width)
        required_size = row_index
        for mask, count in enumerate(dp):
            if count == 0 or mask.bit_count() != required_size:
                continue
            choices = allowed & ~mask
            while choices:
                bit = choices & -choices
                choices -= bit
                target = mask | bit
                next_dp[target] = (next_dp[target] + count) % modulus
        dp = next_dp
    return dp[-1]


def punctured_permanent_mod(adjacency: list[int], root: int, modulus: int) -> int:
    keep = [vertex for vertex in range(N) if vertex != root]
    column_index = {vertex: index for index, vertex in enumerate(keep)}
    rows = []
    for vertex in keep:
        mask = 0
        for neighbor in keep:
            if adjacency[vertex] & (1 << neighbor):
                mask |= 1 << column_index[neighbor]
        rows.append(mask)
    return permanent_mod(rows, N - 1, modulus)


def triangle_degree(adjacency: list[int], root: int) -> int:
    neighbors = [vertex for vertex in range(N) if adjacency[root] & (1 << vertex)]
    return sum(
        bool(adjacency[left] & (1 << right))
        for left, right in itertools.combinations(neighbors, 2)
    )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--models", type=int, default=16)
    parser.add_argument("--timeout-ms", type=int, default=120_000)
    parser.add_argument("--modulus", type=int, default=256)
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

    residues_by_triangle_degree: dict[int, set[int]] = defaultdict(set)
    examples: dict[tuple[int, int], tuple[int, int]] = {}
    for model_index in range(args.models):
        result = solver.check()
        if result != sat:
            print(f"enumeration_stopped={result}; models={model_index}")
            raise SystemExit(2)
        model = solver.model()
        adjacency = [0] * N
        for (left, right), variable in variables.items():
            if is_true(model.eval(variable)):
                adjacency[left] |= 1 << right
                adjacency[right] |= 1 << left
        for root in range(N):
            degree = triangle_degree(adjacency, root)
            residue = punctured_permanent_mod(adjacency, root, args.modulus)
            residues_by_triangle_degree[degree].add(residue)
            examples.setdefault((degree, residue), (model_index, root))
        solver.add(Or([variable != model.eval(variable) for variable in variables.values()]))

    all_residues = set().union(*residues_by_triangle_degree.values())
    print(f"bounded_models={args.models}; rooted_samples={args.models * N}")
    print(
        f"permanent_A_delete_x_mod{args.modulus}_by_triangle_degree="
        f"{dict(sorted((degree, sorted(values)) for degree, values in residues_by_triangle_degree.items()))}"
    )
    print(f"all_residues={sorted(all_residues)}")
    print(f"first_examples={dict(sorted(examples.items()))}")
    print(f"raw_punctured_matching_residue_uniform={len(all_residues) == 1}")


if __name__ == "__main__":
    main()
