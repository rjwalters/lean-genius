#!/usr/bin/env python3
"""Exact F2 completion checks; not an Erdős-85 graph or a graph search.

Rows are bit masks. The fixed control shows that the kernel condition
cannot be dropped from the alternating extension criterion. Its D is
irregular and it fails the internal C4 cap and integer Gram requirements.
"""

from itertools import product


def transpose(rows, columns):
    return [sum(((row >> j) & 1) << i for i, row in enumerate(rows))
            for j in range(columns)]


def mul(a, b):
    result = []
    for row in a:
        value = 0
        for j, other in enumerate(b):
            if row >> j & 1:
                value ^= other
        result.append(value)
    return result


def apply(rows, vector):
    return sum(((row & vector).bit_count() % 2) << i
               for i, row in enumerate(rows))


def rank(rows):
    pivots = {}
    for row in rows:
        while row:
            p = row.bit_length() - 1
            if p in pivots:
                row ^= pivots[p]
            else:
                pivots[p] = row
                break
    return len(pivots)


def alternating(rows):
    return (rows == transpose(rows, len(rows))
            and all(not (row >> i & 1) for i, row in enumerate(rows)))


def fixed_control():
    b = [49, 138, 22, 69, 49, 138, 76, 224]
    h = [38, 145, 25, 100, 70, 137, 152, 98]
    bt = transpose(b, 8)
    assert all(row.bit_count() == 3 for row in b + bt + h)
    assert alternating(h)
    m = mul(b, bt)
    h2 = mul(h, h)
    d = [m[i] ^ (1 << i) ^ 255 ^ h2[i] for i in range(8)]
    c = [row ^ 255 for row in mul(h, b)]
    assert alternating(d)
    assert mul(h, d) == mul(d, h)
    assert alternating(mul(h, d))
    assert alternating(mul(c, bt))
    assert mul(h, m) == mul(m, h)
    assert rank(b) == 6 and rank(m) == 4
    z = (1 << 0) | (1 << 4)
    assert apply(bt, z) == 0
    residual = apply(transpose(c, 8), z)
    assert residual == sum(1 << i for i in (1, 2, 6, 7))
    assert apply(bt, apply(h, z)) == residual
    # Record why this cannot serve as a graph-level counterexample.
    assert sorted(row.bit_count() for row in d) == [1, 1, 3, 3, 3, 3, 3, 3]
    assert (h[0] & h[4]).bit_count() == 2
    assert b[0] == b[4] and b[0].bit_count() == 3
    print("PASS: rank-deficient control has alternating CB^T but B^Tz=0, C^Tz!=0")
    print("Scope: D irregular; H violates C4 cap; no integer Gram or graph completion")


def exhaustive_small_criterion():
    candidates = [[(a << 1) | (b << 2), a | (c << 2), b | (c << 1)]
                  for a, b, c in product(range(2), repeat=3)]
    assert all(alternating(t) for t in candidates)
    checked = 0
    for b_tuple in product(range(8), repeat=2):
        b = list(b_tuple)
        bt = transpose(b, 3)
        image = {apply(b, v) for v in range(8)}
        products = {tuple(mul(b, t)) for t in candidates}
        for c_tuple in product(range(8), repeat=2):
            c = list(c_tuple)
            compatibility = all(col in image for col in transpose(c, 3))
            condition = compatibility and alternating(mul(c, bt))
            assert (c_tuple in products) == condition
            checked += 1
    assert checked == 4096
    print("PASS: all 4096 binary 2x3 B,C pairs satisfy the exact extension criterion")


if __name__ == "__main__":
    fixed_control()
    exhaustive_small_criterion()
