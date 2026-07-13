#!/usr/bin/env python3
"""
Certificate for FourSquareDistributionOQ04M8.lean (the 2k = 8 case of the
hyperoctahedral type-decomposition of sums of squares).

For each n embedded in the Lean file it checks, with exact integers and stdlib
only:

  (a) the EXHAUSTIVE sorted eight-square shape enumeration equals the file's
      shape list (completeness of the case split);
  (b) for each shape, the orbit-size formula
          (star)  orbit = 8! / prod_v (count_v)!  *  2^(#nonzero)
      equals an INDEPENDENT brute count of distinct signed orderings, and equals
      the value embedded in the Lean file;
  (c) sum_shapes orbit == r_8(n), where r_8(n) = #{x in Z^8 : sum x_i^2 = n} is
      computed INDEPENDENTLY by convolving the single-coordinate signed-square
      distribution, and equals the total embedded in the Lean file.

All checks must print PASS. This makes the native_decide values in the Lean file
(authored under a Docker blackout) independently verifiable on the host.
"""

from itertools import combinations_with_replacement, permutations, product
from math import isqrt, factorial
from collections import Counter

# ---- the formula (star) -----------------------------------------------------

def orbit_formula(shape):
    """8! / prod(count!) * 2^(#nonzero)."""
    k = len(shape)
    denom = 1
    for _, m in Counter(shape).items():
        denom *= factorial(m)
    perms = factorial(k) // denom
    nonzero = sum(1 for v in shape if v != 0)
    return perms * (2 ** nonzero)

# ---- independent brute count of signed orderings ----------------------------

def brute_signed_orderings(shape):
    """Number of distinct (x_1,...,x_8) in Z^8 whose multiset of |x_i| is `shape`."""
    seen = set()
    # distinct positions: permutations of the (sorted) absolute values
    for perm in set(permutations(shape)):
        # each nonzero coordinate independently gets a sign; zeros are fixed
        sign_slots = [(-1, 1) if v != 0 else (1,) for v in perm]
        for signs in product(*sign_slots):
            seen.add(tuple(s * v for s, v in zip(signs, perm)))
    return len(seen)

# ---- independent r_8(n) via convolution -------------------------------------

def r_k(n, k):
    base = [0] * (n + 1)
    s = 0
    while s * s <= n:
        base[s * s] += 1 if s == 0 else 2
        s += 1
    dist = [1] + [0] * n
    for _ in range(k):
        new = [0] * (n + 1)
        for a in range(n + 1):
            if dist[a] == 0:
                continue
            for b in range(n + 1 - a):
                if base[b]:
                    new[a + b] += dist[a] * base[b]
        dist = new
    return dist[n]

# ---- exhaustive sorted shapes -----------------------------------------------

def sorted_shapes(n, k=8):
    maxv = isqrt(n)
    res = []
    for combo in combinations_with_replacement(range(maxv + 1), k):
        if sum(v * v for v in combo) == n:
            res.append(combo)
    return res

# ---- values embedded in FourSquareDistributionOQ04M8.lean -------------------

EMBEDDED = {
    1:  ([((0,0,0,0,0,0,0,1), 16)], 16),
    2:  ([((0,0,0,0,0,0,1,1), 112)], 112),
    3:  ([((0,0,0,0,0,1,1,1), 448)], 448),
    4:  ([((0,0,0,0,0,0,0,2), 16), ((0,0,0,0,1,1,1,1), 1120)], 1136),
    5:  ([((0,0,0,0,0,0,1,2), 224), ((0,0,0,1,1,1,1,1), 1792)], 2016),
    6:  ([((0,0,0,0,0,1,1,2), 1344), ((0,0,1,1,1,1,1,1), 1792)], 3136),
    7:  ([((0,0,0,0,1,1,1,2), 4480), ((0,1,1,1,1,1,1,1), 1024)], 5504),
    8:  ([((0,0,0,0,0,0,2,2), 112), ((0,0,0,1,1,1,1,2), 8960),
          ((1,1,1,1,1,1,1,1), 256)], 9328),
    12: ([((0,0,0,0,0,2,2,2), 448), ((0,0,0,0,1,1,1,3), 4480),
          ((0,0,1,1,1,1,2,2), 26880)], 31808),
}

def main():
    ok = True
    for n, (shapes_embedded, total_embedded) in EMBEDDED.items():
        # (a) completeness of the enumeration
        enumerated = sorted_shapes(n)
        embedded_shapes = [sh for sh, _ in shapes_embedded]
        if sorted(enumerated) != sorted(embedded_shapes):
            print(f"n={n}: SHAPE-SET MISMATCH  enum={enumerated}  embedded={embedded_shapes}")
            ok = False
            continue
        # (b) per-shape orbit: formula == brute == embedded
        running = 0
        for sh, c_embedded in shapes_embedded:
            c_formula = orbit_formula(sh)
            c_brute = brute_signed_orderings(sh)
            if not (c_formula == c_brute == c_embedded):
                print(f"n={n} shape={sh}: ORBIT MISMATCH "
                      f"formula={c_formula} brute={c_brute} embedded={c_embedded}")
                ok = False
            running += c_formula
        # (c) totals: sum == r_8(n) == embedded total
        rk = r_k(n, 8)
        if not (running == rk == total_embedded):
            print(f"n={n}: TOTAL MISMATCH  sum={running}  r_8={rk}  embedded={total_embedded}")
            ok = False
        else:
            print(f"n={n}: PASS  r_8={rk}  shapes={len(embedded_shapes)}")
    print("ALL PASS" if ok else "FAILURES PRESENT")
    return 0 if ok else 1

if __name__ == "__main__":
    raise SystemExit(main())
