#!/usr/bin/env python3
"""
S2 certificate for four-square-distribution-oq-04 (2k = 6 case).

Pins the EXACT shapes, per-shape orbit contributions, and per-n totals embedded
in `proofs/Proofs/FourSquareDistributionOQ04.lean`, checking each three ways:

  (a) exhaustive enumeration of sorted six-square shapes for each n;
  (b) the orbit formula (*) 2^(#nonzero) * 6! / prod(mult!) against an
      INDEPENDENT brute count of distinct signed orderings of the shape;
  (c) the per-n total sum_shapes orbit(shape) against r_6(n) computed by an
      INDEPENDENT signed-square convolution.

All exact integer arithmetic.
"""

from itertools import product
from math import factorial, isqrt
from collections import Counter, defaultdict


def shapes(m, n):
    """All sorted m-tuples of nonneg ints whose squares sum to n."""
    top = isqrt(n)
    out = []

    def build(prefix, start, rem, left):
        if left == 0:
            if rem == 0:
                out.append(tuple(prefix))
            return
        v = start
        while v <= top and v * v <= rem:
            build(prefix + [v], v, rem - v * v, left - 1)
            v += 1

    build([], 0, n, m)
    return out


def orbit_formula(shape):
    m = len(shape)
    nz = sum(1 for x in shape if x != 0)
    cnt = Counter(shape)
    perm = factorial(m)
    for c in cnt.values():
        perm //= factorial(c)
    return (2 ** nz) * perm


def orbit_brute(shape):
    """Independent: count distinct signed orderings of the shape's values."""
    seen = set()
    base = shape
    # all sign assignments
    m = len(base)
    for signs in product((1, -1), repeat=m):
        signed = tuple(s * v for s, v in zip(signs, base))
        # all orderings via permutations of indices: use set of permutations
        # (cheap since m=6); collect every permutation of `signed`
        from itertools import permutations as perms
        for p in perms(signed):
            seen.add(p)
    return len(seen)


def r6_convolution(n):
    single = defaultdict(int)
    single[0] = 1
    for x in range(1, isqrt(n) + 1):
        single[x * x] += 2
    dist = defaultdict(int)
    dist[0] = 1
    for _ in range(6):
        nd = defaultdict(int)
        for a, va in dist.items():
            for b, vb in single.items():
                if a + b <= n:
                    nd[a + b] += va * vb
        dist = nd
    return dist[n]


# The exact data embedded in the Lean file.
EXPECTED = {
    1:  [((0, 0, 0, 0, 0, 1), 12)],
    2:  [((0, 0, 0, 0, 1, 1), 60)],
    3:  [((0, 0, 0, 1, 1, 1), 160)],
    5:  [((0, 0, 0, 0, 1, 2), 120), ((0, 1, 1, 1, 1, 1), 192)],
    6:  [((0, 0, 0, 1, 1, 2), 480), ((1, 1, 1, 1, 1, 1), 64)],
    12: [((0, 0, 0, 2, 2, 2), 160), ((0, 0, 1, 1, 1, 3), 960),
         ((1, 1, 1, 1, 2, 2), 960)],
    30: [((0, 0, 0, 1, 2, 5), 960), ((0, 0, 1, 2, 3, 4), 5760),
         ((0, 2, 2, 2, 3, 3), 1920), ((1, 1, 1, 1, 1, 5), 384),
         ((1, 1, 1, 3, 3, 3), 1280), ((1, 1, 2, 2, 2, 4), 3840)],
}
TOTALS = {1: 12, 2: 60, 3: 160, 5: 312, 6: 544, 12: 2080, 30: 14144}


def main():
    for n, exp in EXPECTED.items():
        sh = shapes(6, n)
        # (a) enumeration matches the embedded shape list exactly
        assert set(sh) == {s for s, _ in exp}, \
            f"n={n}: shape set mismatch enum={sorted(sh)} exp={[s for s,_ in exp]}"
        # (b) orbit formula == brute, and == embedded value
        for s, v in exp:
            ofo = orbit_formula(s)
            obr = orbit_brute(s)
            assert ofo == obr == v, \
                f"n={n} shape {s}: formula={ofo} brute={obr} embedded={v}"
        # (c) total == r_6(n) (convolution) == embedded total
        tot = sum(orbit_formula(s) for s in sh)
        r6 = r6_convolution(n)
        assert tot == r6 == TOTALS[n], \
            f"n={n}: sum={tot} r6={r6} embedded={TOTALS[n]}"
        print(f"n={n:>2}: {len(sh)} shapes, sum orbits = r_6(n) = {tot}  OK")

    print("\nALL R6 DECOMPOSITION CERTS PASS")


if __name__ == "__main__":
    main()
