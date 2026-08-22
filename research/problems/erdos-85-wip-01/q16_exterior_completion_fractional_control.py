#!/usr/bin/env python3
"""Exact rational LP control for the q=16 exterior completion problem.

The C6+C26 trace graph has a 156-element component automorphism group.
Quotient the symmetric exterior-edge variables by that group, impose every
cross-block exact-one equation and every no-common-neighbor inequality for
traces sharing a component point, solve the small LP, rationalize the result,
and verify all constraints exactly over Q.
"""

from fractions import Fraction
from itertools import combinations

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix


N = 32
SHORT = tuple(range(6))
LONG = tuple(range(6, 32))


def edge(first: int, second: int) -> tuple[int, int]:
    return tuple(sorted((first, second)))


def cycle(vertices: tuple[int, ...]) -> set[tuple[int, int]]:
    return {
        edge(vertices[index], vertices[(index + 1) % len(vertices)])
        for index in range(len(vertices))
    }


H = cycle(SHORT) | cycle(LONG)

# The explicit alternating-eigenline trace graph found by the reduced SAT
# audit: opposite matching on C6, parity-cross K_{3,13}, and an odd-step
# degree-eleven circulant on C26.
TRACES = {(0, 3), (1, 4), (2, 5)}
TRACES |= {
    edge(first, second)
    for first in SHORT
    for second in LONG
    if first % 2 != (second - 6) % 2
}
for first in range(26):
    for difference in {1, 5, 7, 9, 11, 13, 15, 17, 19, 21, 25}:
        TRACES.add(edge(6 + first, 6 + (first + difference) % 26))
TRACES = tuple(sorted(TRACES))
TRACE_INDEX = {trace: index for index, trace in enumerate(TRACES)}
assert len(TRACES) == 224


def component_image(kind: int, vertex: int) -> int:
    """Four generators for the order-156 trace automorphism group."""
    if vertex < 6:
        if kind == 0:
            return (vertex + 2) % 6
        if kind == 1:
            return vertex
        if kind == 2:
            return (vertex + 1) % 6
        return (-vertex) % 6
    coordinate = vertex - 6
    if kind == 0:
        return vertex
    if kind == 1:
        return 6 + (coordinate + 2) % 26
    if kind == 2:
        return 6 + (coordinate + 1) % 26
    return 6 + (-coordinate) % 26


def sparse_matrix(patterns, columns: int, inequalities: bool = False):
    rows = []
    column_indices = []
    values = []
    for row, pattern in enumerate(patterns):
        if inequalities:
            first, second = pattern
            if first == second:
                rows.append(row)
                column_indices.append(first)
                values.append(2)
            else:
                rows.extend((row, row))
                column_indices.extend((first, second))
                values.extend((1, 1))
        else:
            for column, value in pattern:
                rows.append(row)
                column_indices.append(column)
                values.append(value)
    return coo_matrix(
        (values, (rows, column_indices)), shape=(len(patterns), columns)
    ).tocsr()


def main() -> None:
    admissible = {
        (first, second)
        for first, second in combinations(range(len(TRACES)), 2)
        if not any(
            edge(x, y) in H for x in TRACES[first] for y in TRACES[second]
        )
    }

    generators = []
    for kind in range(4):
        generators.append(
            [
                TRACE_INDEX[
                    edge(component_image(kind, first), component_image(kind, second))
                ]
                for first, second in TRACES
            ]
        )

    parent = {pair: pair for pair in admissible}

    def find(pair):
        while parent[pair] != pair:
            parent[pair] = parent[parent[pair]]
            pair = parent[pair]
        return pair

    def union(first, second) -> None:
        first = find(first)
        second = find(second)
        if first != second:
            parent[second] = first

    for pair in tuple(admissible):
        for generator in generators:
            union(pair, tuple(sorted((generator[pair[0]], generator[pair[1]]))))

    roots = sorted({find(pair) for pair in admissible})
    orbit_index = {root: index for index, root in enumerate(roots)}

    exact_patterns = set()
    for trace_index, trace in enumerate(TRACES):
        excluded = {
            vertex
            for endpoint in trace
            for vertex in range(N)
            if edge(endpoint, vertex) in H
        }
        for vertex in range(N):
            if vertex in excluded:
                continue
            counts = {}
            for other_index, other_trace in enumerate(TRACES):
                pair = tuple(sorted((trace_index, other_index)))
                if (
                    other_index != trace_index
                    and vertex in other_trace
                    and pair in admissible
                ):
                    orbit = orbit_index[find(pair)]
                    counts[orbit] = counts.get(orbit, 0) + 1
            exact_patterns.add(tuple(sorted(counts.items())))

    inequality_patterns = set()
    for first, second in combinations(range(len(TRACES)), 2):
        if not (set(TRACES[first]) & set(TRACES[second])):
            continue
        for witness in range(len(TRACES)):
            first_pair = tuple(sorted((first, witness)))
            second_pair = tuple(sorted((second, witness)))
            if (
                witness not in (first, second)
                and first_pair in admissible
                and second_pair in admissible
            ):
                first_orbit = orbit_index[find(first_pair)]
                second_orbit = orbit_index[find(second_pair)]
                inequality_patterns.add(tuple(sorted((first_orbit, second_orbit))))

    exact_patterns = sorted(exact_patterns)
    inequality_patterns = sorted(inequality_patterns)
    exact_matrix = sparse_matrix(exact_patterns, len(roots))
    inequality_matrix = sparse_matrix(
        inequality_patterns, len(roots), inequalities=True
    )

    result = linprog(
        np.zeros(len(roots)),
        A_ub=inequality_matrix,
        b_ub=np.ones(len(inequality_patterns)),
        A_eq=exact_matrix,
        b_eq=np.ones(len(exact_patterns)),
        bounds=(0, 1),
        method="highs",
    )
    assert result.success, result.message

    rational = [Fraction(float(value)).limit_denominator(1_000_000)
                for value in result.x]
    for row in range(exact_matrix.shape[0]):
        total = sum(
            Fraction(int(value)) * rational[column]
            for column, value in zip(
                exact_matrix[row].indices, exact_matrix[row].data
            )
        )
        assert total == 1
    for row in range(inequality_matrix.shape[0]):
        total = sum(
            Fraction(int(value)) * rational[column]
            for column, value in zip(
                inequality_matrix[row].indices, inequality_matrix[row].data
            )
        )
        assert total <= 1
    assert all(0 <= value <= 1 for value in rational)

    print(f"verified exact rational fractional control: {len(roots)} orbit variables")
    print(
        f"constraints: {len(exact_patterns)} exact, "
        f"{len(inequality_patterns)} intersecting-trace C4 types"
    )
    print(f"maximum denominator: {max(value.denominator for value in rational)}")


if __name__ == "__main__":
    main()
