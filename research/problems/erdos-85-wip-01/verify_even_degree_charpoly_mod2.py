#!/usr/bin/env python3
"""Realize every x^2 f(x)^2 over F_2 by a simple even-degree graph.

Checks the construction through order 12 using matching parity to compute
characteristic polynomials independently. No exact regularity, C4-freeness,
connectedness, or prescribed adjacency square is claimed. Standard library.
"""

from functools import lru_cache


def dot(a, b):
    return (a & b).bit_count() % 2


def multiply(a, b):
    """Multiply square F_2 matrices stored as bitset rows."""
    result = []
    for row in a:
        value = 0
        while row:
            bit = row & -row
            value ^= b[bit.bit_length() - 1]
            row ^= bit
        result.append(value)
    return result


def inverse(a):
    n = len(a)
    rows = [row | (1 << (n + i)) for i, row in enumerate(a)]
    for j in range(n):
        pivot = next(i for i in range(j, n) if rows[i] >> j & 1)
        rows[j], rows[pivot] = rows[pivot], rows[j]
        for i in range(n):
            if i != j and rows[i] >> j & 1:
                rows[i] ^= rows[j]
    assert [row & ((1 << n) - 1) for row in rows] == [1 << i for i in range(n)]
    return [row >> n for row in rows]


def construct(n, coefficients):
    """f=x^(n/2-1)+sum_i coefficients[i] x^i, encoded as bits."""
    assert n >= 2 and n % 2 == 0
    r = n // 2 - 1
    assert 0 <= coefficients < 1 << r
    remaining = [(1 << i) | (1 << (n - 2)) for i in range(n - 2)]
    us, vs = [], []
    while remaining:
        u = remaining.pop(0)
        j = next(i for i, v in enumerate(remaining) if dot(u, v))
        v = remaining.pop(j)
        remaining = [z ^ (u if dot(z, v) else 0) ^ (v if dot(z, u) else 0)
                     for z in remaining]
        us.append(u)
        vs.append(v)
    columns = [(1 << n) - 1, 1 << (n - 1)] + us + vs
    basis = [sum(((column >> i) & 1) << j for j, column in enumerate(columns))
             for i in range(n)]
    # Companion T of f, then C=0_2 direct-sum T direct-sum T^T.
    t = [(int(i > 0) << (i - 1) if i else 0)
         | (((coefficients >> i) & 1) << (r - 1)) for i in range(r)]
    transpose = [sum(((row >> j) & 1) << i for i, row in enumerate(t))
                 for j in range(r)]
    c = [0, 0] + [row << 2 for row in t] + [row << (2 + r) for row in transpose]
    return multiply(multiply(basis, c), inverse(basis))


def characteristic_mod2(a):
    """Sachs parity: reversing longer cycles cancels them in characteristic 2."""
    @lru_cache(None)
    def matchings(mask):
        if not mask:
            return 1
        bit = mask & -mask
        i = bit.bit_length() - 1
        rest = mask ^ bit
        polynomial = matchings(rest)  # i is unmatched
        neighbors = a[i] & rest
        while neighbors:
            other = neighbors & -neighbors
            polynomial ^= matchings(rest ^ other) << 1
            neighbors ^= other
        return polynomial

    n = len(a)
    parity = matchings((1 << n) - 1)
    return sum(((parity >> k) & 1) << (n - 2 * k) for k in range(n // 2 + 1))


def main():
    total = 0
    for n in range(2, 13, 2):
        r = n // 2 - 1
        observed = set()
        for coefficients in range(1 << r):
            a = construct(n, coefficients)
            assert all(not (row >> i & 1) for i, row in enumerate(a))
            assert all(row.bit_count() % 2 == 0 for row in a)
            assert all((a[i] >> j & 1) == (a[j] >> i & 1)
                       for i in range(n) for j in range(n))
            assert a[-1] == 0  # Explicit limitation: this construction has an isolate.
            expected = (1 << n) | sum(((coefficients >> i) & 1) << (2 * i + 2)
                                     for i in range(r))
            actual = characteristic_mod2(a)
            assert actual == expected
            observed.add(actual)
        assert len(observed) == 1 << r
        total += len(observed)
        print(f"n={n}: all {len(observed)} permitted polynomials realized")
    print(f"PASS: {total} exact constructions; no A-REG conclusion")


if __name__ == "__main__":
    main()
