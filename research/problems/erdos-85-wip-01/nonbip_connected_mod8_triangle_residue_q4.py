#!/usr/bin/env python3
"""All-model q=4 probe for the proposed local mod-8 NONBIP residue.

For A, let D join pairs with no common A-neighbor and let K=A∩D.  At a
root x, write t_x for its triangle degree and B_x for the number of
triangles not containing x that meet N_A(x).  C4-freeness makes that
intersection a singleton, so (At)_x = 2 t_x + B_x and

    (Ak)_x = q^2 - 2 (At)_x.

The uniform target needed by the selected divergence-75 route is only
(Ak)_x = 4 mod 8, equivalently (At)_x = 2 mod 4.
"""

from __future__ import annotations

import argparse
import itertools
from collections import Counter, defaultdict

from z3 import And, Bool, If, Or, Solver, Sum, is_true, sat


Q = 4
N = Q * Q
ROOT_NEIGHBORS = set(range(1, Q + 1))


def profile(edges: list[tuple[int, int]]) -> list[tuple[int, int, int, int, int]]:
    adjacency = [[False] * N for _ in range(N)]
    for left, right in edges:
        adjacency[left][right] = adjacency[right][left] = True

    triangles = [
        triple
        for triple in itertools.combinations(range(N), 3)
        if all(adjacency[left][right] for left, right in itertools.combinations(triple, 2))
    ]
    triangle_degree = [sum(vertex in triple for triple in triangles) for vertex in range(N)]
    common = [
        [sum(adjacency[left][middle] and adjacency[middle][right] for middle in range(N)) for right in range(N)]
        for left in range(N)
    ]
    k_degree = [
        sum(adjacency[vertex][other] and common[vertex][other] == 0 for other in range(N))
        for vertex in range(N)
    ]

    answer = []
    for root in range(N):
        neighborhood = {vertex for vertex in range(N) if adjacency[root][vertex]}
        external = sum(root not in triple and len(neighborhood.intersection(triple)) == 1 for triple in triangles)
        at = sum(triangle_degree[vertex] for vertex in neighborhood)
        ak = sum(k_degree[vertex] for vertex in neighborhood)
        assert at == 2 * triangle_degree[root] + external
        assert ak == Q * Q - 2 * at
        answer.append((triangle_degree[root], external, at, k_degree[root], ak))
    return answer


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--models", type=int, default=256)
    parser.add_argument("--timeout-ms", type=int, default=120_000)
    args = parser.parse_args()

    solver = Solver()
    solver.set(timeout=args.timeout_ms, random_seed=850075)
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
        solver.add(Sum([If(edge(vertex, other), 1, 0) for other in range(N) if other != vertex]) == Q)
    for left, right in itertools.combinations(range(N), 2):
        solver.add(
            Sum([
                If(And(edge(left, middle), edge(right, middle)), 1, 0)
                for middle in range(N)
                if middle != left and middle != right
            ]) <= 1
        )

    joint_profiles: Counter[tuple[int, int, int, int, int]] = Counter()
    external_by_t: dict[int, Counter[int]] = defaultdict(Counter)
    for index in range(args.models):
        result = solver.check()
        if result != sat:
            print(f"enumeration_stopped={result}; models={index}")
            raise SystemExit(2)
        model = solver.model()
        edges = [pair for pair, variable in variables.items() if is_true(model.eval(variable))]
        vertex_profiles = profile(edges)
        for entry in vertex_profiles:
            t, external, at, _k, ak = entry
            joint_profiles[entry] += 1
            external_by_t[t][external] += 1
            if ak % 8 != 4 or at % 4 != 2 or (external + 2 * t) % 4 != 2:
                print(f"residue_falsifier_model={index}; profile={entry}; edges={edges}")
                raise SystemExit(1)
        solver.add(Or([variable != model.eval(variable) for variable in variables.values()]))

    print(f"bounded_models={args.models}")
    print(f"joint_profiles(t,B,At,k,Ak)={dict(sorted(joint_profiles.items()))}")
    print(f"external_by_t={dict(sorted((t, dict(sorted(counts.items()))) for t, counts in external_by_t.items()))}")
    print("Ak_mod_8_eq_4_universal_on_sample=true")
    print("At_mod_4_eq_2_universal_on_sample=true")
    print("external_plus_2t_mod_4_eq_2_universal_on_sample=true")


if __name__ == "__main__":
    main()
