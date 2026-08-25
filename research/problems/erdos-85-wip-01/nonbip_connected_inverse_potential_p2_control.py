#!/usr/bin/env python3
"""Exact control showing that the Laplacian equation (P2) does not imply
source/sink sign separation.

The graph below is connected and 3-regular on 16 vertices.  With q=4 and
S={0,6,12,15}, the uniquely normalized solution of

    L_D x = 1_S - (1/4)1,   sum x = 1/4

has positive values at the sinks 10 and 14.  Consequently any proof of (P8)
in NONBIP_CONNECTED_INVERSE_POTENTIAL_AUDIT.md must use the self-indexed
block-sum law (P3), not the maximum principle or (P2) alone.
"""

from collections import deque
from fractions import Fraction


Q = 4
N = 16
SOURCE = {0, 6, 12, 15}
EDGES = {
    (0, 2), (0, 4), (0, 15), (1, 2), (1, 3), (1, 6),
    (2, 9), (3, 9), (3, 13), (4, 7), (4, 9), (5, 11),
    (5, 13), (5, 14), (6, 8), (6, 14), (7, 12), (7, 13),
    (8, 10), (8, 11), (10, 11), (10, 15), (12, 14), (12, 15),
}


def solve(matrix: list[list[Fraction]], rhs: list[Fraction]) -> list[Fraction]:
    """Gauss-Jordan elimination over Q."""
    augmented = [row[:] + [value] for row, value in zip(matrix, rhs)]
    for column in range(len(matrix)):
        pivot = next(row for row in range(column, len(matrix))
                     if augmented[row][column])
        augmented[column], augmented[pivot] = augmented[pivot], augmented[column]
        scale = augmented[column][column]
        augmented[column] = [value / scale for value in augmented[column]]
        for row in range(len(matrix)):
            if row == column:
                continue
            scale = augmented[row][column]
            if scale:
                augmented[row] = [
                    x - scale * y
                    for x, y in zip(augmented[row], augmented[column])
                ]
    return [row[-1] for row in augmented]


def main() -> None:
    neighbors = [set() for _ in range(N)]
    for u, v in EDGES:
        neighbors[u].add(v)
        neighbors[v].add(u)
    assert all(len(neighbors[v]) == Q - 1 for v in range(N))

    reached = {0}
    queue = deque([0])
    while queue:
        u = queue.popleft()
        for v in neighbors[u] - reached:
            reached.add(v)
            queue.append(v)
    assert len(reached) == N

    laplacian = [
        [Fraction(Q - 1 if i == j else -int(j in neighbors[i]))
         for j in range(N)]
        for i in range(N)
    ]
    forcing = [
        Fraction(Q - 1, Q) if i in SOURCE else Fraction(-1, Q)
        for i in range(N)
    ]
    # Replace one dependent Laplacian equation by the normalization.
    laplacian[-1] = [Fraction(1) for _ in range(N)]
    forcing[-1] = Fraction(1, Q)
    potential = solve(laplacian, forcing)

    assert sum(potential) == Fraction(1, Q)
    assert all(
        sum(potential[i] - potential[j] for j in neighbors[i])
        == (Fraction(Q - 1, Q) if i in SOURCE else Fraction(-1, Q))
        for i in range(N)
    )
    positive_sinks = [i for i in range(N) if i not in SOURCE and potential[i] > 0]
    assert positive_sinks == [10, 14]

    print("verified connected cubic P2 control on 16 vertices")
    print("positive sinks:", positive_sinks)
    print("x[10] =", potential[10], "x[14] =", potential[14])


if __name__ == "__main__":
    main()
