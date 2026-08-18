#!/usr/bin/env python3
"""Exact independent census for the two lambda-six component strata.

Unlike ``r_classify.py``, this checker does not assume a hand-written basis
for the symmetric zero-one commutant.  It gives Z3 one Boolean variable for
each of the 120 unordered vertex pairs and imposes the defining equations
directly.  The resulting labeled solutions are grouped up to isomorphism of
their forced defect graphs.

Requires ``z3-solver`` and ``networkx``.
"""

from __future__ import annotations

import itertools

import networkx as nx
import z3


N = 16


def cycle_matrix(parts: tuple[int, ...]) -> list[list[int]]:
    matrix = [[0] * N for _ in range(N)]
    start = 0
    for length in parts:
        for index in range(length):
            left = start + index
            right = start + (index + 1) % length
            matrix[left][right] = matrix[right][left] = 1
        start += length
    assert start == N
    return matrix


def matrix_square(matrix: list[list[int]]) -> list[list[int]]:
    return [
        [sum(matrix[u][w] * matrix[w][v] for w in range(N)) for v in range(N)]
        for u in range(N)
    ]


def classify(parts: tuple[int, ...]) -> tuple[int, list[tuple[int, int, bool]]]:
    h = cycle_matrix(parts)
    h2 = matrix_square(h)
    pairs = list(itertools.combinations(range(N), 2))
    variables = {pair: z3.Bool(f"r_{'_'.join(map(str, parts))}_{pair[0]}_{pair[1]}") for pair in pairs}

    def r(u: int, v: int) -> z3.BoolRef:
        if u == v:
            return z3.BoolVal(False)
        return variables[min(u, v), max(u, v)]

    solver = z3.Solver()
    for u, v in pairs:
        if h2[u][v] != 0:
            solver.add(z3.Not(r(u, v)))
    for u in range(N):
        solver.add(z3.PbEq([(r(u, v), 1) for v in range(N) if u != v], 6))
    for u in range(N):
        for v in range(N):
            solver.add(
                z3.Sum([z3.If(r(u, w), h[w][v], 0) for w in range(N)])
                == z3.Sum([z3.If(r(w, v), h[u][w], 0) for w in range(N)])
            )

    representatives: list[nx.Graph] = []
    multiplicities: list[int] = []
    labeled_count = 0
    while solver.check() == z3.sat:
        model = solver.model()
        bits = {
            pair: z3.is_true(model.eval(variable, model_completion=True))
            for pair, variable in variables.items()
        }
        labeled_count += 1
        defect = nx.Graph()
        defect.add_nodes_from(range(N))
        for u, v in pairs:
            entry = 1 - h2[u][v] - int(bits[u, v])
            if entry not in (0, 1):
                raise AssertionError(f"non-Boolean defect entry {entry} at {(u, v)}")
            if entry:
                defect.add_edge(u, v)
        if set(dict(defect.degree()).values()) != {7}:
            raise AssertionError("forced defect is not seven-regular")
        if not nx.is_connected(defect):
            raise AssertionError("forced defect is disconnected")

        for index, representative in enumerate(representatives):
            if nx.is_isomorphic(defect, representative):
                multiplicities[index] += 1
                break
        else:
            representatives.append(defect)
            multiplicities.append(1)

        solver.add(z3.Or([
            z3.Not(variables[pair]) if value else variables[pair]
            for pair, value in bits.items()
        ]))

    classes = sorted(
        (
            multiplicity,
            sum(nx.triangles(graph).values()) // 3,
            nx.is_bipartite(graph),
        )
        for graph, multiplicity in zip(representatives, multiplicities)
    )
    print(f"{parts}: labeled={labeled_count}, classes={classes}")
    return labeled_count, classes


def main() -> int:
    ten_six = classify((10, 6))
    five_five_three_three = classify((5, 5, 3, 3))
    expected_ten_six = (144, [(48, 0, True), (48, 30, False), (48, 40, False)])
    expected_five = (360, [(120, 0, True), (120, 30, False), (120, 40, False)])
    return 0 if ten_six == expected_ten_six and five_five_three_three == expected_five else 1


if __name__ == "__main__":
    raise SystemExit(main())
