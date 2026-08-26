#!/usr/bin/env python3
"""Cut cycle-length-only fractional weights for signed matching exchange.

On the exact q=4 control, count the sign-changing alternating switches of
each half-length 4,6,...,16 at the first twelve Levi perfect matchings.  A
weight depending only on half-length would normalize every matching exactly
when this count matrix times the weight vector is the all-ones vector.  Exact
rational ranks show that system is inconsistent.
"""

import sympy as sp

from binary_q4_fixed_free_disconnected_control import A_EDGES, N, adjacency


LENGTHS = list(range(4, N + 1, 2))


def cycle_counts(matching: tuple[int, ...], neighbors: list[set[int]]) -> list[int]:
    outgoing = [
        [j for j in range(N) if j != i and matching[j] in neighbors[i]]
        for i in range(N)
    ]
    answer = {length: 0 for length in LENGTHS}

    def search(root: int, vertex: int, seen: set[int], length: int) -> None:
        for target in outgoing[vertex]:
            new_length = length + 1
            if target == root and new_length >= 4 and new_length % 2 == 0:
                answer[new_length] += 1
            elif target > root and target not in seen:
                search(root, target, seen | {target}, new_length)

    for root in range(N):
        search(root, root, {root}, 0)
    return [answer[length] for length in LENGTHS]


def main() -> None:
    neighbors = adjacency(A_EDGES)
    matchings: list[tuple[int, ...]] = []

    def enumerate_matchings(row: int, used: set[int], prefix: list[int]) -> None:
        if len(matchings) >= 12:
            return
        if row == N:
            matchings.append(tuple(prefix))
            return
        for column in sorted(neighbors[row] - used):
            enumerate_matchings(row + 1, used | {column}, prefix + [column])

    enumerate_matchings(0, set(), [])
    assert len(matchings) == 12
    rows = [cycle_counts(matching, neighbors) for matching in matchings]
    expected = [
        [11, 73, 289, 727, 1059, 787, 104],
        [16, 74, 246, 794, 1364, 910, 104],
        [18, 41, 253, 846, 1329, 841, 90],
        [11, 55, 284, 720, 1149, 728, 75],
        [11, 55, 284, 720, 1149, 728, 75],
        [13, 58, 274, 798, 1305, 876, 100],
        [16, 74, 246, 794, 1364, 910, 104],
        [11, 73, 289, 727, 1059, 787, 104],
        [11, 55, 284, 720, 1149, 728, 75],
        [18, 88, 342, 768, 1000, 702, 92],
        [13, 72, 296, 744, 1173, 871, 111],
        [12, 95, 319, 792, 1134, 738, 86],
    ]
    assert rows == expected
    matrix = sp.Matrix(rows)
    augmented = matrix.row_join(sp.ones(len(rows), 1))
    assert matrix.rank() == 7
    assert augmented.rank() == 8

    print("verified q=4 cycle-length fractional-weight obstruction")
    print("half-lengths =", LENGTHS)
    print("count rank = 7; augmented rank = 8; no normalization exists")


if __name__ == "__main__":
    main()
