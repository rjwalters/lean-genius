#!/usr/bin/env python3
"""
Durable verification cert for lagrange-four-squares-oq-01-oq-03.

OQ-01-OQ-03: "What is the exact count of four-square representations of n, and can
the Jacobi four-square formula r4(n) = 8 * sum_{d|n, 4 does-not-divide d} d be
formalized?"

Here r4(n) := #{ (x1,x2,x3,x4) in Z^4 : x1^2 + x2^2 + x3^2 + x4^2 = n }, counting
ORDERED, SIGNED quadruples (so e.g. r4(1) = 8: one coord is +-1, three are 0).

**Jacobi's four-square theorem** (1834): for every n >= 1,
        r4(n) = 8 * sum_{ d | n, 4 !| d } d.
Equivalent closed forms (also checked):
  * n odd        :  r4(n) = 8  * sigma(n)
  * n even       :  r4(n) = 24 * sigma(m), where m = largest odd divisor of n.

This cert brute-forces r4(n) (signed lattice-point count) and compares it to the
divisor-sum formula for n = 1..N, and independently cross-checks the two odd/even
closed forms. It is a regression oracle for any future Lean formalization and
pins down EXACTLY which arithmetic function the formula computes (sign/order
conventions are the usual formalization trap).

Pure stdlib. r4 brute force is O(N^2) lattice points per n; N=120 runs in ~1s.
"""

from math import isqrt


def r4_bruteforce(n):
    """Count ordered signed (x1,x2,x3,x4) in Z^4 with sum of squares = n."""
    if n == 0:
        return 1  # the all-zero quadruple
    b = isqrt(n)
    # precompute squares and their multiplicity contribution via two-square counts
    # r2(k) = #{(a,b) in Z^2 : a^2+b^2 = k}; then r4(n) = sum_k r2(k) r2(n-k).
    r2 = [0] * (n + 1)
    for a in range(-b, b + 1):
        a2 = a * a
        if a2 > n:
            continue
        rem = n - a2
        rb = isqrt(rem)
        for bb in range(-rb, rb + 1):
            s = a2 + bb * bb
            if s <= n:
                r2[s] += 1
    total = 0
    for k in range(n + 1):
        total += r2[k] * r2[n - k]
    return total


def divisors(n):
    ds = []
    i = 1
    while i * i <= n:
        if n % i == 0:
            ds.append(i)
            if i != n // i:
                ds.append(n // i)
        i += 1
    return sorted(ds)


def jacobi_formula(n):
    """8 * sum of divisors d of n with 4 does-not-divide d."""
    return 8 * sum(d for d in divisors(n) if d % 4 != 0)


def sigma(n):
    return sum(divisors(n))


def odd_part(n):
    while n % 2 == 0:
        n //= 2
    return n


def closed_form(n):
    """Odd/even split closed form (independent re-derivation of jacobi_formula)."""
    if n % 2 == 1:
        return 8 * sigma(n)
    return 24 * sigma(odd_part(n))


def main():
    N = 120
    fails = 0
    spot = {1: 8, 2: 24, 3: 32, 4: 24, 5: 48, 6: 96, 7: 64}
    for n in range(1, N + 1):
        r = r4_bruteforce(n)
        j = jacobi_formula(n)
        c = closed_form(n)
        if not (r == j == c):
            fails += 1
            print(f"[FAIL] n={n}: r4={r}, jacobi={j}, closed_form={c}")
        if n in spot and r != spot[n]:
            fails += 1
            print(f"[FAIL] spot-check n={n}: r4={r} != expected {spot[n]}")

    print(f"Checked n = 1..{N}: r4(n) == 8*sum_{{d|n,4!|d}}d == odd/even closed form.")
    print("Spot anchors: r4(1)=8, r4(2)=24, r4(3)=32, r4(4)=24, r4(5)=48, r4(7)=64.")
    # sanity: r4(4)=24 (NOT 8*sigma(4)=56) because d=4 is excluded by 4 !| d.
    assert jacobi_formula(4) == 24, "the 4 !| d exclusion is load-bearing at n=4"
    assert 8 * sigma(4) == 56, "naive 8*sigma would give the WRONG value at n=4"

    print("\n=== RESULT ===")
    if fails == 0:
        print("ALL CHECKS PASSED: Jacobi's four-square count formula verified, n=1..120.")
        print("Mathlib has Lagrange EXISTENCE (Nat.sum_four_squares) but not this COUNT;")
        print("the n=4 case shows the `4 does-not-divide d` exclusion is essential")
        print("(naive 8*sigma(4)=56 != r4(4)=24). See knowledge.md for the formalization path.")
    else:
        print(f"{fails} FAILURES present.")
        raise SystemExit(1)


if __name__ == "__main__":
    main()
