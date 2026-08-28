#!/usr/bin/env python3
"""Verify the cyclic tile-intertwiner countermodel at representative q."""


def matmul(left, right):
    n = len(left)
    return [
        [sum(left[i][k] * right[k][j] for k in range(n)) for j in range(n)]
        for i in range(n)
    ]


def transpose(matrix):
    return [list(row) for row in zip(*matrix)]


def add(matrices):
    n = len(matrices[0])
    return [[sum(matrix[i][j] for matrix in matrices) for j in range(n)] for i in range(n)]


def translation(n, shift):
    return [[int(j == (i + shift) % n) for j in range(n)] for i in range(n)]


def verify(q):
    n = 2 * q
    connection = {q}
    for step in range(1, q // 2):
        connection.add(step)
        connection.add((-step) % n)
    assert len(connection) == q - 1

    translations = [translation(n, shift) for shift in range(n)]
    defect = add([translations[shift] for shift in sorted(connection)])
    assert all(defect[i][i] == 0 for i in range(n))
    assert all(sum(row) == q - 1 for row in defect)

    # The steps 1 and 2 give connectivity and the triangle 0,1,2.
    assert 1 in connection and 2 in connection

    groups = [list(range(start, start + 4)) for start in range(0, n, 4)]
    assert len(groups) == q // 2
    tiles = [add([translations[shift] for shift in group]) for group in groups]
    reverse_tiles = [
        add([translations[(-shift) % n] for shift in group]) for group in groups
    ]

    ones = [[1] * n for _ in range(n)]
    assert add(tiles) == ones
    for tile, reverse in zip(tiles, reverse_tiles):
        assert all(value in (0, 1) for row in tile for value in row)
        assert all(sum(row) == 4 for row in tile)
        assert all(sum(tile[i][j] for i in range(n)) == 4 for j in range(n))
        assert matmul(defect, tile) == matmul(tile, defect)
        assert transpose(tile) == reverse

    # Each consecutive four-shift tile is itself the product of two
    # zero-one 2-regular matrices.  This verifies local rectangle
    # factorization, but makes no claim that the factors can be reused
    # coherently across different endpoint pairs.
    first_factor = add([translations[0], translations[1]])
    for group, tile in zip(groups, tiles):
        start = group[0]
        second_factor = add(
            [translations[start], translations[(start + 2) % n]]
        )
        for factor in (first_factor, second_factor):
            assert all(value in (0, 1) for row in factor for value in row)
            assert all(sum(row) == 2 for row in factor)
            assert all(sum(factor[i][j] for i in range(n)) == 2 for j in range(n))
        assert matmul(first_factor, second_factor) == tile


def main():
    for q in (8, 16, 32):
        verify(q)
    print("size-two tile-intertwiner countermodel: PASS (q=8,16,32)")


if __name__ == "__main__":
    main()
