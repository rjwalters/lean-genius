#!/usr/bin/env python3
"""Exact 2-adic constant-kernel lift audit on a faithful q=4 control."""

from __future__ import annotations

import collections

import sympy


N = 16
EDGES = (
    (0, 1), (0, 2), (0, 3), (0, 4), (1, 4), (1, 12), (1, 15),
    (2, 5), (2, 8), (2, 11), (3, 7), (3, 9), (3, 14), (4, 6),
    (4, 13), (5, 7), (5, 8), (5, 10), (6, 9), (6, 10), (6, 13),
    (7, 10), (7, 14), (8, 9), (8, 12), (9, 12), (10, 15),
    (11, 13), (11, 14), (11, 15), (12, 15), (13, 14),
)


def matrix() -> list[list[int]]:
    result = [[0] * N for _ in range(N)]
    for left, right in EDGES:
        result[left][right] = result[right][left] = 1
    return result


def syndrome_table(adjacency: list[list[int]]) -> dict[tuple[int, ...], list[tuple[int, ...]]]:
    table: dict[tuple[int, ...], list[tuple[int, ...]]] = collections.defaultdict(list)
    for bits in range(1 << N):
        vector = tuple((bits >> index) & 1 for index in range(N))
        syndrome = tuple(
            sum(adjacency[row][column] * vector[column] for column in range(N)) & 1
            for row in range(N)
        )
        table[syndrome].append(vector)
    return table


def main() -> None:
    adjacency = matrix()
    neighbors = [
        {column for column, value in enumerate(row) if value}
        for row in adjacency
    ]
    assert all(len(row) == 4 for row in neighbors)
    assert max(
        len(neighbors[left] & neighbors[right])
        for left in range(N) for right in range(left + 1, N)
    ) <= 1
    exact = sympy.Matrix(adjacency)
    assert exact.rank() == 15
    primitive_kernel = [int(value) for value in exact.nullspace()[0]]
    assert set(primitive_kernel) == {-1, 1}

    table = syndrome_table(adjacency)
    assert len(table[(0,) * N]) == 4
    states = {tuple([1] * N)}
    counts = [len(states)]
    # A*1=4*1, so start with a kernel vector modulo 2^2.
    for exponent in range(2, 10):
        next_states: set[tuple[int, ...]] = set()
        for state in states:
            product = [
                sum(adjacency[row][column] * state[column] for column in range(N))
                for row in range(N)
            ]
            assert all(value % (1 << exponent) == 0 for value in product)
            rhs = tuple((-(value >> exponent)) & 1 for value in product)
            for correction in table.get(rhs, ()):
                next_states.add(tuple(
                    (state[index] + (1 << exponent) * correction[index])
                    % (1 << (exponent + 1))
                    for index in range(N)
                ))
        states = next_states
        counts.append(len(states))
        if not states:
            break

    print(f"rank_Q={exact.rank()}")
    print(f"kernel_generator={primitive_kernel}")
    print(f"kernel_dimension_F2=2")
    print(f"lift_state_counts={counts}")
    print(f"first_failed_modulus={1 << (len(counts) + 1)}")
    assert counts == [1, 4, 16, 64, 0]


if __name__ == "__main__":
    main()
