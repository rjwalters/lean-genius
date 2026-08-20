#!/usr/bin/env python3
"""Exact q=9 repair test for the finite-field dot-product graph Gamma_a.

Use GF(9) = GF(3)[t]/(t^2+1).  On the 80 nonzero vectors in GF(9)^2,
join distinct u,v when u dot v = a for a nonzero field element.  Linear
algebra makes this graph C4-free.  It has 72 vertices of degree 9 and the
eight points of u dot u = a have degree 8 (their missing incidence is a
discarded loop).

The cheapest possible regularization is to add a perfect matching on those
eight deficient vertices.  This script exhausts all 105 matchings and also
checks the stronger fact that no single missing edge among the eight can be
added while preserving C4-freeness.
"""

from __future__ import annotations

import itertools
import json

Field = tuple[int, int]
Vector = tuple[Field, Field]


def add(x: Field, y: Field) -> Field:
    return ((x[0] + y[0]) % 3, (x[1] + y[1]) % 3)


def mul(x: Field, y: Field) -> Field:
    # t^2 = -1 in GF(3)[t]/(t^2+1).
    return (
        (x[0] * y[0] - x[1] * y[1]) % 3,
        (x[0] * y[1] + x[1] * y[0]) % 3,
    )


def dot(u: Vector, v: Vector) -> Field:
    return add(mul(u[0], v[0]), mul(u[1], v[1]))


def perfect_matchings(vertices: tuple[int, ...]):
    if not vertices:
        yield ()
        return
    first = vertices[0]
    for index in range(1, len(vertices)):
        second = vertices[index]
        rest = vertices[1:index] + vertices[index + 1:]
        for matching in perfect_matchings(rest):
            yield ((first, second),) + matching


def c4_free(adjacency: list[set[int]]) -> bool:
    return all(
        len(adjacency[u] & adjacency[v]) <= 1
        for u in range(len(adjacency))
        for v in range(u + 1, len(adjacency))
    )


def add_edges(adjacency: list[set[int]], edges) -> list[set[int]]:
    result = [neighbors.copy() for neighbors in adjacency]
    for u, v in edges:
        result[u].add(v)
        result[v].add(u)
    return result


def main() -> None:
    field = list(itertools.product(range(3), repeat=2))
    zero = (0, 0)
    vectors = [
        (x, y) for x in field for y in field if (x, y) != (zero, zero)
    ]

    reports = []
    for value in field[1:]:
        adjacency = [set() for _ in vectors]
        for u, vector_u in enumerate(vectors):
            for v in range(u + 1, len(vectors)):
                if dot(vector_u, vectors[v]) == value:
                    adjacency[u].add(v)
                    adjacency[v].add(u)

        assert c4_free(adjacency)
        deficient = tuple(
            vertex for vertex, neighbors in enumerate(adjacency)
            if len(neighbors) == 8
        )
        assert len(deficient) == 8
        assert sum(len(neighbors) == 9 for neighbors in adjacency) == 72
        assert all(v not in adjacency[u]
                   for u, v in itertools.combinations(deficient, 2))

        safe_edges = [
            (u, v) for u, v in itertools.combinations(deficient, 2)
            if c4_free(add_edges(adjacency, [(u, v)]))
        ]
        matching_count = 0
        safe_matchings = []
        for matching in perfect_matchings(deficient):
            matching_count += 1
            if c4_free(add_edges(adjacency, matching)):
                safe_matchings.append(matching)
        assert matching_count == 105
        reports.append({
            "dot_product_value": value,
            "degree_8_vertices": len(deficient),
            "degree_9_vertices": 72,
            "individually_safe_added_edges": len(safe_edges),
            "perfect_matchings_checked": matching_count,
            "safe_perfect_matchings": len(safe_matchings),
        })

    print(json.dumps({"field": "GF(3)[t]/(t^2+1)", "reports": reports},
                     sort_keys=True))


if __name__ == "__main__":
    main()
