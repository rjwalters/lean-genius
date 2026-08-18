#!/usr/bin/env python3
"""Exact colored-order census for the two lambda-six R strata.

This repeats the direct 120-variable equations from
``check_lambda6_classification.py`` and computes the degree sequence of
``H ∩ D`` for every labeled solution.  In a graph realization this is the
triangle-free edge graph on the defect component, so every degree must be
zero or two.  Requires ``z3-solver`` and ``networkx``.
"""

from __future__ import annotations

from collections import Counter
import itertools

import networkx as nx
import z3

from check_lambda6_classification import N, cycle_matrix, matrix_square


Record = tuple[int, bool, int, bool, tuple[tuple[int, int], ...]]


def census(parts: tuple[int, ...]) -> Counter[Record]:
    h = cycle_matrix(parts)
    h2 = matrix_square(h)
    pairs = list(itertools.combinations(range(N), 2))
    variables = {pair: z3.Bool(f"r_{parts}_{pair}") for pair in pairs}

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

    result: Counter[Record] = Counter()
    while solver.check() == z3.sat:
        model = solver.model()
        bits = {
            pair: z3.is_true(model.eval(variable, model_completion=True))
            for pair, variable in variables.items()
        }
        defect = [[0] * N for _ in range(N)]
        graph = nx.Graph()
        graph.add_nodes_from(range(N))
        for u, v in pairs:
            entry = 1 - h2[u][v] - int(bits[u, v])
            assert entry in (0, 1)
            defect[u][v] = defect[v][u] = entry
            if entry:
                graph.add_edge(u, v)

        color_degrees = [
            sum(h[u][v] * defect[u][v] for v in range(N)) for u in range(N)
        ]
        record = (
            sum(nx.triangles(graph).values()) // 3,
            nx.is_bipartite(graph),
            sum(degree == 2 for degree in color_degrees),
            all(degree in (0, 2) for degree in color_degrees),
            tuple(sorted(Counter(color_degrees).items())),
        )
        result[record] += 1
        solver.add(
            z3.Or(
                [
                    z3.Not(variables[pair]) if value else variables[pair]
                    for pair, value in bits.items()
                ]
            )
        )
    return result


EXPECTED_VALID = {
    (10, 6): Counter(
        {
            (0, True, 16, True, ((2, 16),)): 2,
            (30, False, 16, True, ((2, 16),)): 2,
            (40, False, 6, True, ((0, 10), (2, 6))): 2,
        }
    ),
    (5, 5, 3, 3): Counter(
        {
            (0, True, 0, True, ((0, 16),)): 120,
            (30, False, 10, True, ((0, 6), (2, 10))): 120,
            (40, False, 10, True, ((0, 6), (2, 10))): 120,
        }
    ),
}


def main() -> int:
    ok = True
    for parts, expected in EXPECTED_VALID.items():
        full = census(parts)
        valid = Counter({record: count for record, count in full.items() if record[3]})
        print(f"{parts}: total={sum(full.values())}, valid={sum(valid.values())}")
        for record, count in sorted(valid.items()):
            print(f"  {count}: {record}")
        ok &= valid == expected
        ok &= sum(full.values()) == (144 if parts == (10, 6) else 360)
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
