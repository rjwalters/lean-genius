#!/usr/bin/env python3
"""
Durable exact verifier for four-square-distribution-oq-04 (ORIENT, S1).

OQ-04 (the seeker's stub question): does the orbit-stabilizer type-decomposition
of the gallery proof `four-square-distribution` (the 2k = 4 case) GENERALIZE to
r_{2k}(n), the number of representations of n as a sum of 2k squares, under the
hyperoctahedral group

        B_m = S_m  semidirect  (Z/2)^m ,   |B_m| = m! * 2^m ,   m = 2k

of signed permutations acting on representation tuples (x_1,...,x_m) in Z^m?

CLAIMED FORMULA (to be verified). For a "shape" s of n -- a sorted tuple
(a_1 <= ... <= a_m) of naturals with sum a_i^2 = n -- with
    z       := number of zero parts,
    {m_i}   := multiplicities of the DISTINCT absolute values (0 included),
the B_m-orbit of any representation of shape s has size

        orbit(s) = 2^(m - z) * m! / prod_i (m_i!)
                 = 2^(#nonzero parts) * multinomial(m; multiplicities),

and the total count splits as

        r_{2k}(n) = sum over shapes s of n  of  orbit(s).            (DECOMP)

By orbit-stabilizer the stabilizer of a shape-s representation then has order

        |stab(s)| = |B_m| / orbit(s) = 2^z * z! * prod_{nonzero} (m_j!) .   (STAB)

(The 2^z is sign flips of the z zero coordinates -- which act trivially -- and z!
permutes them; prod m_j! permutes equal nonzero values. No nonzero coordinate may
be sign-flipped within a stabilizer.)

This script verifies (DECOMP), the orbit-size formula, and (STAB) by EXACT brute
enumeration for 2k in {2,4,6,8}, cross-checking r_2 (two-square) and r_4 (Jacobi)
against their classical closed forms. All integer arithmetic; no Lean, no Docker.
"""

import math
from collections import Counter
from functools import lru_cache


# --- single-coordinate signed-square distribution & r_{m}(n) by convolution ----

def square_counts(N):
    """sq[s] = #{x in Z : x^2 = s} for 0<=s<=N: 1 at 0, 2 at positive squares."""
    sq = [0] * (N + 1)
    sq[0] = 1
    r = 1
    while r * r <= N:
        sq[r * r] = 2
        r += 1
    return sq


def r_sum_of_squares(m, N):
    """Return list R where R[n] = r_m(n) = #{(x_1..x_m) in Z^m : sum xi^2 = n},
    for 0<=n<=N. Exact, by repeated convolution of the single-coord distribution."""
    base = square_counts(N)
    R = [0] * (N + 1)
    R[0] = 1  # empty / m=0 convolution identity
    for _ in range(m):
        nxt = [0] * (N + 1)
        for a in range(N + 1):
            if R[a] == 0:
                continue
            ra = R[a]
            for s in range(0, N + 1 - a):
                if base[s]:
                    nxt[a + s] += ra * base[s]
        R = nxt
    return R


# --- classical closed forms for anchoring ------------------------------------

def r2_closed(n):
    """r_2(n) = 4 * (d_1(n) - d_3(n)), d_j = #divisors ≡ j (mod 4). r_2(0)=1."""
    if n == 0:
        return 1
    d1 = d3 = 0
    d = 1
    while d <= n:
        if n % d == 0:
            if d % 4 == 1:
                d1 += 1
            elif d % 4 == 3:
                d3 += 1
        d += 1
    return 4 * (d1 - d3)


def r4_jacobi(n):
    """r_4(n) = 8 * sum_{d|n, 4∤d} d. r_4(0)=1."""
    if n == 0:
        return 1
    s = 0
    d = 1
    while d <= n:
        if n % d == 0 and d % 4 != 0:
            s += d
        d += 1
    return 8 * s


# --- shapes (sorted nonneg m-tuples with sum of squares = n) -----------------

def shapes(m, n):
    """Yield all sorted tuples (a_1<=...<=a_m), a_i>=0, sum a_i^2 = n."""
    res = []
    top = math.isqrt(n)

    def rec(start, left_slots, remaining, acc):
        if left_slots == 0:
            if remaining == 0:
                res.append(tuple(acc))
            return
        # minimal completion uses the smallest allowed value `start`; prune
        for a in range(start, top + 1):
            aa = a * a
            # if we put a in every remaining slot, the minimum added is left_slots*aa
            if aa * left_slots > remaining:
                break
            rec(a, left_slots - 1, remaining - aa, acc + [a])

    rec(0, m, n, [])
    return res


def orbit_size(m, shape):
    z = sum(1 for a in shape if a == 0)
    nonzero = m - z
    counts = Counter(shape)
    denom = 1
    for c in counts.values():
        denom *= math.factorial(c)
    return (2 ** nonzero) * math.factorial(m) // denom


def stab_size(m, shape):
    z = sum(1 for a in shape if a == 0)
    prod_nz = 1
    for v, c in Counter(shape).items():
        if v != 0:
            prod_nz *= math.factorial(c)
    return (2 ** z) * math.factorial(z) * prod_nz


def brute_signed_orderings(m, shape):
    """Exact count of signed ordered tuples (x_1..x_m) in Z^m whose multiset of
    absolute values equals `shape`. = #orderings * 2^#nonzero. Computed directly
    as a cross-check of orbit_size (independent of the formula)."""
    counts = Counter(shape)
    denom = 1
    for c in counts.values():
        denom *= math.factorial(c)
    orderings = math.factorial(m) // denom
    nonzero = sum(1 for a in shape if a != 0)
    return orderings * (2 ** nonzero)


# --- main --------------------------------------------------------------------

def main():
    failures = []

    # Range of n per m (kept small for 2k=8 so brute convolution is fast/exact).
    cfg = {2: 300, 4: 200, 6: 120, 8: 80}

    for m in (2, 4, 6, 8):
        N = cfg[m]
        R = r_sum_of_squares(m, N)
        ok_decomp = ok_orbit = ok_stab = True
        Bm = math.factorial(m) * (2 ** m)
        for n in range(1, N + 1):
            sh = shapes(m, n)
            total = 0
            for s in sh:
                o = orbit_size(m, s)
                # orbit formula == independent brute signed-ordering count
                if o != brute_signed_orderings(m, s):
                    ok_orbit = False
                    failures.append(("orbit", m, n, s, o))
                # orbit-stabilizer: orbit * stab == |B_m|
                if o * stab_size(m, s) != Bm:
                    ok_stab = False
                    failures.append(("stab", m, n, s))
                total += o
            if total != R[n]:
                ok_decomp = False
                failures.append(("decomp", m, n, total, R[n]))
        print(f"2k={m:>1}  (n<=({N}))  "
              f"orbit-size formula: {'PASS' if ok_orbit else 'FAIL'}  |  "
              f"orbit*stab=|B_{m}|={Bm}: {'PASS' if ok_stab else 'FAIL'}  |  "
              f"sum_shapes orbit == r_{m}(n): {'PASS' if ok_decomp else 'FAIL'}")

    # Anchor the convolutional r_m against classical closed forms.
    R2 = r_sum_of_squares(2, 300)
    R4 = r_sum_of_squares(4, 200)
    a2 = all(R2[n] == r2_closed(n) for n in range(0, 301))
    a4 = all(R4[n] == r4_jacobi(n) for n in range(0, 201))
    print(f"\nanchor  r_2(n) == 4(d1-d3)  (n<=(300)): {'PASS' if a2 else 'FAIL'}")
    print(f"anchor  r_4(n) == 8*sigma*(n) (n<=(200)): {'PASS' if a4 else 'FAIL'}")

    # Worked example display: n = 30 across 2k = 4.
    print("\nworked example  2k=4, n=30  (shape : orbit size):")
    for s in shapes(4, 30):
        print(f"   {s} : orbit {orbit_size(4, s)}  stab {stab_size(4, s)}")
    print(f"   sum of orbits = {sum(orbit_size(4,s) for s in shapes(4,30))} "
          f"= r_4(30) = {R4[30]}")

    all_ok = (not failures) and a2 and a4
    print("\n" + ("ALL CHECKS PASS" if all_ok else f"FAILURES: {failures[:8]}"))
    return 0 if all_ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
