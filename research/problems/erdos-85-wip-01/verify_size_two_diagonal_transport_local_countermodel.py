#!/usr/bin/env python3
"""Verify the uniform local diagonal-transport countermodel."""


def translation(n, shift):
    return [[int(j == (i + shift) % n) for j in range(n)] for i in range(n)]


def add(left, right):
    return [[x + y for x, y in zip(a, b)] for a, b in zip(left, right)]


def multiply(left, right):
    n = len(left)
    return [
        [sum(left[i][k] * right[k][j] for k in range(n)) for j in range(n)]
        for i in range(n)
    ]


def transpose(matrix):
    return [list(row) for row in zip(*matrix)]


def connected(matrix):
    seen = {0}
    stack = [0]
    while stack:
        i = stack.pop()
        for j, value in enumerate(matrix[i]):
            if value and j not in seen:
                seen.add(j)
                stack.append(j)
    return len(seen) == len(matrix)


def support(matrix):
    return {(i, j) for i, row in enumerate(matrix) for j, value in enumerate(row)
            if value}


def verify(q):
    n = 2 * q
    shifts = [translation(n, shift) for shift in range(n)]
    source = add(shifts[1], shifts[-1])
    target = add(shifts[3], shifts[-3])
    cross = add(shifts[0], shifts[n // 2])

    for diagonal in (source, target):
        assert diagonal == transpose(diagonal)
        assert all(diagonal[i][i] == 0 for i in range(n))
        assert all(sum(row) == 2 for row in diagonal)
        assert connected(diagonal)

    assert all(sum(row) == 2 for row in cross)
    assert all(sum(column) == 2 for column in transpose(cross))

    first = multiply(source, cross)
    second = multiply(cross, target)
    for tile in (first, second):
        assert all(value in (0, 1) for row in tile for value in row)
        assert all(sum(row) == 4 for row in tile)
        assert all(sum(column) == 4 for column in transpose(tile))
    assert support(first).isdisjoint(support(second))


def main():
    for q in (8, 16, 32):
        verify(q)
    print("local diagonal transport countermodel: PASS (q=8,16,32)")


if __name__ == "__main__":
    main()
