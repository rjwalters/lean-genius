#!/usr/bin/env python3
"""Exact induced-order-81 search inside the orthogonal polarity graph ER_9.

The orthogonal polarity graph on PG(2, 9) is C4-free, has 91 vertices, ten
vertices of degree 9, and 81 vertices of degree 10.  An induced 81-vertex
minimum-degree-9 graph would therefore arise from a ten-vertex deletion set S
such that every retained degree-9 vertex loses no neighbor and every retained
degree-10 vertex loses at most one neighbor.

This script constructs GF(9) and PG(2, 9) directly, checks the polarity graph,
and asks Z3 for precisely such a deletion set.  The instance has only 91
Boolean variables.  UNSAT closes this natural geometric construction class;
it is not a proof that no C4-free minimum-degree-9 graph on 81 vertices exists.
"""

from __future__ import annotations

import itertools
import json

import z3

Field = tuple[int, int]
Point = tuple[Field, Field, Field]

ZERO: Field = (0, 0)
ONE: Field = (1, 0)
FIELD: tuple[Field, ...] = tuple(itertools.product(range(3), repeat=2))


def add(x: Field, y: Field) -> Field:
    return ((x[0] + y[0]) % 3, (x[1] + y[1]) % 3)


def mul(x: Field, y: Field) -> Field:
    # GF(9) = GF(3)[t]/(t^2+1), so t^2 = -1.
    return (
        (x[0] * y[0] - x[1] * y[1]) % 3,
        (x[0] * y[1] + x[1] * y[0]) % 3,
    )


def inverse(x: Field) -> Field:
    if x == ZERO:
        raise ZeroDivisionError
    return next(y for y in FIELD if mul(x, y) == ONE)


def normalize(vector: Point) -> Point:
    first = next(x for x in vector if x != ZERO)
    scale = inverse(first)
    return tuple(mul(scale, x) for x in vector)  # type: ignore[return-value]


def dot(x: Point, y: Point) -> Field:
    result = ZERO
    for a, b in zip(x, y):
        result = add(result, mul(a, b))
    return result


def polarity_graph() -> tuple[list[Point], list[set[int]]]:
    points = sorted({
        normalize(vector)
        for vector in itertools.product(FIELD, repeat=3)
        if any(x != ZERO for x in vector)
    })
    adjacency = [set() for _ in points]
    for i in range(len(points)):
        for j in range(i + 1, len(points)):
            if dot(points[i], points[j]) == ZERO:
                adjacency[i].add(j)
                adjacency[j].add(i)
    return points, adjacency


def main() -> None:
    points, adjacency = polarity_graph()
    assert len(points) == 9 * 9 + 9 + 1 == 91
    degree_histogram = {
        degree: sum(len(neighbors) == degree for neighbors in adjacency)
        for degree in {len(neighbors) for neighbors in adjacency}
    }
    assert degree_histogram == {9: 10, 10: 81}
    max_common = max(
        len(adjacency[u] & adjacency[v])
        for u in range(91) for v in range(u + 1, 91)
    )
    assert max_common == 1

    deleted = [z3.Bool(f"deleted_{vertex}") for vertex in range(91)]
    solver = z3.Solver()
    solver.add(z3.PbEq([(variable, 1) for variable in deleted], 10))
    for vertex, neighbors in enumerate(adjacency):
        lost_degree = z3.Sum([
            z3.If(deleted[neighbor], 1, 0) for neighbor in neighbors
        ])
        solver.add(z3.Implies(
            z3.Not(deleted[vertex]),
            lost_degree <= len(neighbors) - 9,
        ))

    result = solver.check()
    assert result == z3.unsat
    absolute = {v for v, neighbors in enumerate(adjacency)
                if len(neighbors) == 9}
    absolute_neighbor_histogram = {
        count: sum(
            v not in absolute and len(adjacency[v] & absolute) == count
            for v in range(91)
        )
        for count in range(3)
    }
    print(json.dumps({
        "field": "GF(3)[t]/(t^2+1)",
        "projective_points": len(points),
        "degree_histogram": degree_histogram,
        "maximum_common_neighbors": max_common,
        "deleted_vertices_required": 10,
        "retained_minimum_degree_required": 9,
        "absolute_neighbor_histogram_on_nonabsolute_points":
            absolute_neighbor_histogram,
        "result": str(result).upper(),
        "scope": "induced 81-vertex subgraphs of ER_9 only",
    }, sort_keys=True))


if __name__ == "__main__":
    main()
