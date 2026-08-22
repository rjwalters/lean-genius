#!/usr/bin/env python3
"""Exhaust the direct fixed-point-free repair of the affine polarity control.

For GF(4) and GF(8), delete all diagonal incidences and replace them by every
perfect matching on the absolute points.  Each repair stays symmetric and
q-regular and has connected defect graph, but exactly q(q-1) unordered pairs
have two common neighbors, so it is not C4-free.
"""

from __future__ import annotations


FIELDS = {4: (2, 0b111), 8: (3, 0b1011)}


def mul(a: int, b: int, degree: int, polynomial: int) -> int:
    result = 0
    while b:
        if b & 1:
            result ^= a
        b >>= 1
        a <<= 1
        if a >> degree:
            a ^= polynomial
    return result & ((1 << degree) - 1)


def matchings(items: tuple[int, ...]):
    if not items:
        yield ()
        return
    first = items[0]
    for i in range(1, len(items)):
        second = items[i]
        rest = items[1:i] + items[i + 1 :]
        for tail in matchings(rest):
            yield ((first, second),) + tail


def component_count(graph: list[list[int]]) -> int:
    unseen = set(range(len(graph)))
    count = 0
    while unseen:
        count += 1
        stack = [unseen.pop()]
        while stack:
            u = stack.pop()
            neighbors = {v for v, edge in enumerate(graph[u]) if edge}
            fresh = neighbors & unseen
            unseen -= fresh
            stack.extend(fresh)
    return count


def check(q: int) -> bool:
    degree, polynomial = FIELDS[q]
    points = [(a, b) for a in range(q) for b in range(q)]
    n = q * q
    base = [
        [int(d == (mul(a, c, degree, polynomial) ^ b)) for c, d in points]
        for a, b in points
    ]
    absolute = tuple(i for i in range(n) if base[i][i])
    outcomes = set()
    total = 0
    for matching in matchings(absolute):
        total += 1
        adjacency = [row[:] for row in base]
        for i in absolute:
            adjacency[i][i] = 0
        for i, j in matching:
            adjacency[i][j] = adjacency[j][i] = 1
        common = [
            [sum(adjacency[i][z] * adjacency[j][z] for z in range(n))
             for j in range(n)]
            for i in range(n)
        ]
        repeated = sum(
            common[i][j] == 2 for i in range(n) for j in range(i + 1, n)
        )
        defect = [
            [int(i != j and common[i][j] == 0) for j in range(n)]
            for i in range(n)
        ]
        outcomes.add((
            tuple(sorted({sum(row) for row in adjacency})),
            repeated,
            component_count(defect),
        ))
    expected = {((q,), q * (q - 1), 1)}
    ok = outcomes == expected
    print(f"q={q} matchings={total} outcomes={sorted(outcomes)} verified={ok}")
    return ok


if __name__ == "__main__":
    verified = all(check(q) for q in FIELDS)
    print(f"affine_polarity_matching_repair_verified={verified}")
    raise SystemExit(0 if verified else 1)
