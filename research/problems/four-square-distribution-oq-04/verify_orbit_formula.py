#!/usr/bin/env python3
"""
Brute-force confirmation of the hyperoctahedral orbit-size formula (★) used by
FourSquareDistributionOQ04Decomp.lean / ...Sign.lean.

For every m-tuple of integers with sum of squares = n, group by `shape` (the
sorted multiset of absolute values) and check that each fiber has size

    shapeContribution(m, shape) = (m! / prod_v count_v!) * 2^{#nonzero}.

Also separately confirms the sign-count half (signFiber_card):
    for fixed abs-profile g, #{f : |f i| = g i} = 2^{#{i : g i != 0}}.
"""
from itertools import product
from collections import Counter
from math import factorial, prod


def fiber_sizes(m, n):
    box = range(-n, n + 1)
    fibers = Counter()
    for f in product(box, repeat=m):
        if sum(x * x for x in f) == n:
            fibers[tuple(sorted(abs(x) for x in f))] += 1
    return fibers


def shape_contribution(m, shape):
    c = Counter(shape)
    arrangements = factorial(m) // prod(factorial(k) for k in c.values())
    nonzero = sum(1 for v in shape if v != 0)
    return arrangements * 2 ** nonzero


def check_orbit():
    mismatch = checked = 0
    for m in range(2, 6):
        for n in range(0, 13):
            for shape, sz in fiber_sizes(m, n).items():
                checked += 1
                if shape_contribution(m, shape) != sz:
                    mismatch += 1
                    print(f"  MISMATCH m={m} n={n} shape={shape} "
                          f"actual={sz} formula={shape_contribution(m, shape)}")
    print(f"(orbit) checked {checked} fibers (m<=5, n<=12), mismatches={mismatch}")
    return mismatch == 0


def check_sign():
    mismatch = checked = 0
    for m in range(1, 6):
        for g in product(range(-2, 3), repeat=m):
            fiber = [f for f in product(range(-2, 3), repeat=m)
                     if all(abs(f[i]) == abs(g[i]) for i in range(m))]
            expected = 2 ** sum(1 for x in g if x != 0)
            checked += 1
            if len(fiber) != expected:
                mismatch += 1
                print(f"  SIGN MISMATCH m={m} g={g} actual={len(fiber)} formula={expected}")
    print(f"(sign) checked {checked} abs-profiles (m<=5), mismatches={mismatch}")
    return mismatch == 0


if __name__ == "__main__":
    ok = check_orbit() and check_sign()
    print("RESULT:", "PASS" if ok else "FAIL")
    raise SystemExit(0 if ok else 1)
