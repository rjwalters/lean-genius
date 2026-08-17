#!/usr/bin/env python3
"""Exact audit of square tree counts for 7-regular circulants on Z/16.

This is a guardrail for the order-64 seven-defect-component branch.  That
branch forces the residual determinant of its connected 16-vertex component
to be a square and gives the complement a 2-factor plus six-perfect-matching
decomposition.  The audit shows that those two necessary conditions alone do
not yield a contradiction.

Only the Python standard library is used.  Kirchhoff cofactors are evaluated
with fraction-free Bareiss elimination, so every reported value is exact.
"""

from __future__ import annotations

import itertools
import math


ORDER = 16
ANTIPODE = ORDER // 2
PAIRS = tuple((step, ORDER - step) for step in range(1, ANTIPODE))


def bareiss_determinant(matrix: list[list[int]]) -> int:
    """Return an exact integer determinant by fraction-free elimination."""
    work = [row[:] for row in matrix]
    size = len(work)
    if size == 0:
        return 1
    sign = 1
    previous = 1
    for pivot_index in range(size - 1):
        if work[pivot_index][pivot_index] == 0:
            swap = next(
                (row for row in range(pivot_index + 1, size)
                 if work[row][pivot_index] != 0),
                None,
            )
            if swap is None:
                return 0
            work[pivot_index], work[swap] = work[swap], work[pivot_index]
            sign = -sign
        pivot = work[pivot_index][pivot_index]
        for row in range(pivot_index + 1, size):
            for column in range(pivot_index + 1, size):
                numerator = (
                    work[row][column] * pivot
                    - work[row][pivot_index] * work[pivot_index][column]
                )
                quotient, remainder = divmod(numerator, previous)
                if remainder:
                    raise AssertionError("Bareiss division was not exact")
                work[row][column] = quotient
        previous = pivot
        for row in range(pivot_index + 1, size):
            work[row][pivot_index] = 0
    return sign * work[-1][-1]


def tree_count(connections: frozenset[int]) -> int:
    """Kirchhoff tree count of the corresponding circulant graph."""
    laplacian = [[0] * ORDER for _ in range(ORDER)]
    degree = len(connections)
    for vertex in range(ORDER):
        laplacian[vertex][vertex] = degree
        for step in connections:
            laplacian[vertex][(vertex + step) % ORDER] = -1
    cofactor = [row[:-1] for row in laplacian[:-1]]
    return bareiss_determinant(cofactor)


def connected(connections: frozenset[int]) -> bool:
    """A cyclic Cayley graph is connected iff its steps generate Z/n."""
    return math.gcd(ORDER, *connections) == 1


def complement_pairs(connections: frozenset[int]) -> tuple[tuple[int, int], ...]:
    """The four inverse pairs in the 8-regular complement."""
    return tuple(pair for pair in PAIRS if pair[0] not in connections)


def main() -> int:
    cases = 0
    connected_cases = 0
    square_cases: list[tuple[tuple[int, ...], int, int]] = []
    for selected_pairs in itertools.combinations(PAIRS, 3):
        connections = frozenset(
            {ANTIPODE} | {step for pair in selected_pairs for step in pair}
        )
        cases += 1
        count = tree_count(connections)
        if not connected(connections):
            if count != 0:
                raise AssertionError("disconnected graph has nonzero cofactor")
            continue
        connected_cases += 1
        root = math.isqrt(count)
        if root * root == count:
            complement = complement_pairs(connections)
            if len(complement) != 4:
                raise AssertionError("complement does not have four step pairs")
            # Any complement pair can be the ambient 2-factor.  Each of the
            # other three even-cycle pair graphs splits into two perfect
            # matchings, yielding the required six matchings.
            square_cases.append((tuple(sorted(connections)), count, root))

    if (cases, connected_cases, len(square_cases)) != (35, 34, 12):
        raise AssertionError("unexpected circulant census")
    witness = ((1, 2, 4, 8, 12, 14, 15), 428171305104, 654348)
    if witness not in square_cases:
        raise AssertionError("canonical square-tree witness missing")

    print(f"cases={cases} connected={connected_cases} square={len(square_cases)}")
    for connections, count, root in square_cases:
        complement = complement_pairs(frozenset(connections))
        print(
            f"S={connections} tau={count}={root}^2 "
            f"complement_pairs={complement}"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
