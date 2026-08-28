#!/usr/bin/env python3
"""Verify a local q=8 cyclic-block odd-triangle countermodel.

This is deliberately not a full all-size-two block family.  It shows that
connectedness of three reciprocal 2-regular blocks plus zero-one pair
products does not force their triangle trace to be even.
"""

N = 16

ROW_SUPPORTS = [
    [
        (7, 14), (1, 6), (0, 9), (11, 13),
        (4, 15), (2, 14), (5, 10), (4, 5),
        (9, 12), (0, 6), (3, 15), (1, 3),
        (8, 10), (11, 12), (7, 8), (2, 13),
    ],
    [
        (2, 9), (14, 15), (4, 7), (8, 11),
        (1, 5), (9, 13), (1, 3), (8, 12),
        (4, 10), (5, 15), (0, 11), (6, 13),
        (3, 12), (0, 2), (6, 10), (7, 14),
    ],
    [
        (7, 11), (6, 10), (3, 10), (2, 4),
        (1, 6), (4, 14), (0, 2), (9, 13),
        (9, 12), (0, 7), (8, 11), (5, 14),
        (13, 15), (3, 5), (8, 15), (1, 12),
    ],
]


def matrix(rows):
    out = [[0] * N for _ in range(N)]
    for i, support in enumerate(rows):
        assert len(set(support)) == 2
        for j in support:
            out[i][j] = 1
    return out


def transpose(a):
    return [list(row) for row in zip(*a)]


def multiply(a, b):
    bt = transpose(b)
    return [[sum(x * y for x, y in zip(row, col)) for col in bt]
            for row in a]


def trace(a):
    return sum(a[i][i] for i in range(N))


def assert_two_regular(a):
    assert all(sum(row) == 2 for row in a)
    assert all(sum(col) == 2 for col in transpose(a))


def assert_connected_bipartite(a):
    adjacency = [set() for _ in range(2 * N)]
    for i, row in enumerate(a):
        for j, value in enumerate(row):
            if value:
                adjacency[i].add(N + j)
                adjacency[N + j].add(i)
    seen = {0}
    stack = [0]
    while stack:
        vertex = stack.pop()
        for neighbor in adjacency[vertex] - seen:
            seen.add(neighbor)
            stack.append(neighbor)
    assert len(seen) == 2 * N
    # A connected 2-regular graph on 32 vertices is one C_32.
    assert all(len(neighbors) == 2 for neighbors in adjacency)


def main():
    a, b, c = map(matrix, ROW_SUPPORTS)
    for block in (a, b, c):
        assert_two_regular(block)
        assert_connected_bipartite(block)

    for product in (multiply(a, b), multiply(b, c), multiply(c, a)):
        assert all(value in (0, 1) for row in product for value in row)
        assert all(sum(row) == 4 for row in product)
        assert all(sum(col) == 4 for col in transpose(product))

    abc = multiply(multiply(a, b), c)
    assert trace(abc) == 7

    # Reversing the color orientation transposes all three blocks and leaves
    # the same cyclic trace, as required by reciprocal ambient placement.
    reverse = multiply(multiply(transpose(c), transpose(b)), transpose(a))
    assert trace(reverse) == 7

    print("verified: three C32 blocks, binary 4-regular pair products, trace 7")


if __name__ == "__main__":
    main()
