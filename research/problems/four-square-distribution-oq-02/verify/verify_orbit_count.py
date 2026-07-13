#!/usr/bin/env python3
"""
Reproducible verification for four-square-distribution-oq-02.

Open question: bound the number of distinct representation TYPES of n as a sum
of four squares (i.e. the number of orbits of the hyperoctahedral group
B_4 = (Z/2)^4 rtimes S_4 acting on solution vectors) in terms of r_4(n) and
divisor data.

This script independently verifies, from first principles (brute force, no
appeal to the formulas being tested), the following claims that the ORIENT
survey relies on:

  (A) Jacobi's formula      r_4(n) = 8 * sigma*(n),  sigma*(n) = sum_{d|n, 4 nmid d} d.
  (B) Orbit-size formula    |orbit(v)| = 2^k * 4!/prod_v(mult_v!),
                            k = #nonzero coords, mult over distinct |values| (0 incl.).
  (C) Orbit-sum identity    sum_{types t} |orbit(t)| = r_4(n).
  (D) numTypes(n) = #{(a<=b<=c<=d) in N^4 : a^2+b^2+c^2+d^2 = n}.
  (E) Candidate bounds relating numTypes(n) to r_4(n).

Every assertion is checked by brute-force enumeration of the actual signed,
ordered solution vectors, so the script is self-contained and does not assume
the very formulas it certifies.
"""

from collections import Counter
from math import isqrt, factorial


# ---------------------------------------------------------------------------
# Ground truth: brute-force enumeration of ALL ordered signed solutions.
# ---------------------------------------------------------------------------
def r4_bruteforce(n):
    """Number of ORDERED, SIGNED (x1,x2,x3,x4) in Z^4 with sum xi^2 = n."""
    return len(ordered_signed_solutions(n))


def ordered_signed_solutions(n):
    """All ordered signed integer 4-tuples summing (of squares) to n."""
    b = isqrt(n)
    sols = []
    rng = range(-b, b + 1)
    for x1 in rng:
        s1 = x1 * x1
        if s1 > n:
            continue
        for x2 in rng:
            s2 = s1 + x2 * x2
            if s2 > n:
                continue
            for x3 in rng:
                s3 = s2 + x3 * x3
                if s3 > n:
                    continue
                rem = n - s3
                r = isqrt(rem)
                if r * r == rem:
                    if r == 0:
                        sols.append((x1, x2, x3, 0))
                    else:
                        sols.append((x1, x2, x3, r))
                        sols.append((x1, x2, x3, -r))
    return sols


# ---------------------------------------------------------------------------
# (A) Jacobi's formula via divisor sum.
# ---------------------------------------------------------------------------
def sigma_star(n):
    """sum of divisors d of n with 4 nmid d."""
    if n == 0:
        return 0
    total = 0
    for d in range(1, n + 1):
        if n % d == 0 and d % 4 != 0:
            total += d
    return total


def r4_jacobi(n):
    return 8 * sigma_star(n)


# ---------------------------------------------------------------------------
# Types = orbits. A type is the sorted multiset of absolute values.
# ---------------------------------------------------------------------------
def types(n):
    """Distinct types: sorted tuples (a,b,c,d), 0<=a<=b<=c<=d, sum sq = n."""
    out = set()
    b = isqrt(n)
    for a in range(0, b + 1):
        if a * a > n:
            break
        for bb in range(a, b + 1):
            if a * a + bb * bb > n:
                break
            for c in range(bb, b + 1):
                s = a * a + bb * bb + c * c
                if s > n:
                    break
                rem = n - s
                d = isqrt(rem)
                if d * d == rem and d >= c:
                    out.add((a, bb, c, d))
    return sorted(out)


def orbit_size_formula(t):
    """|orbit| = 2^k * 4!/prod(mult!), k=#nonzero, mult over distinct values."""
    k = sum(1 for x in t if x != 0)
    mult = Counter(t)
    denom = 1
    for m in mult.values():
        denom *= factorial(m)
    return (2 ** k) * factorial(4) // denom


def orbit_size_bruteforce(t, n):
    """True orbit size = #distinct ordered signed vectors with |.|-multiset t."""
    target = tuple(sorted(t))
    seen = set()
    for v in ordered_signed_solutions(n):
        if tuple(sorted(abs(x) for x in v)) == target:
            seen.add(v)
    return len(seen)


# ---------------------------------------------------------------------------
# Verification driver.
# ---------------------------------------------------------------------------
def main():
    NMAX = 400
    print(f"Verifying n = 1 .. {NMAX}\n")

    # (A) + (C): Jacobi and orbit-sum identity.
    for n in range(1, NMAX + 1):
        r_bf = r4_bruteforce(n)
        r_jac = r4_jacobi(n)
        assert r_bf == r_jac, f"Jacobi mismatch n={n}: bf={r_bf} jac={r_jac}"

        ts = types(n)
        orbit_sum = 0
        for t in ts:
            of = orbit_size_formula(t)
            ob = orbit_size_bruteforce(t, n)
            assert of == ob, f"orbit-size mismatch n={n} t={t}: formula={of} bf={ob}"
            orbit_sum += of
        assert orbit_sum == r_bf, f"orbit-sum mismatch n={n}: {orbit_sum} != {r_bf}"

    print("(A) Jacobi r_4(n) = 8*sigma*(n):           OK for 1..%d" % NMAX)
    print("(B) orbit-size formula = brute force:      OK for all types")
    print("(C) sum_t |orbit(t)| = r_4(n):             OK for 1..%d" % NMAX)
    print("(D) numTypes(n) = #(a<=b<=c<=d) solutions: OK by construction\n")

    # (E) Explore candidate bounds: numTypes(n) vs r_4(n) and divisor data.
    # Minimum positive orbit size achievable bounds numTypes from above.
    print("Exploring bounds. For n>0, minimum orbit size over realized types:")
    worst_ratio = 0.0
    worst_n = None
    min_orbit_global = 10**9
    for n in range(1, NMAX + 1):
        ts = types(n)
        if not ts:
            continue
        sizes = [orbit_size_formula(t) for t in ts]
        mn = min(sizes)
        min_orbit_global = min(min_orbit_global, mn)
        nt = len(ts)
        r = r4_bruteforce(n)
        # crude bound numTypes <= r_4(n) / min_orbit_size
        ratio = nt / (r / mn)  # = nt*mn/r ; how tight crude bound is (<=1)
        if ratio > worst_ratio:
            worst_ratio = ratio
            worst_n = n
    print(f"  global minimum orbit size (n in 1..{NMAX}): {min_orbit_global}")

    # Sharper, always-valid bound: every type has orbit size >= 8 (since any
    # nonzero solution has at least one nonzero coordinate => 2^1 * 4!/4! = ...).
    # Check the true minimum orbit size by degeneracy class.
    print("\nMinimum orbit size by structural class (k nonzero, repetition):")
    examples = {}
    for n in range(1, NMAX + 1):
        for t in types(n):
            k = sum(1 for x in t if x != 0)
            sz = orbit_size_formula(t)
            key = (k, tuple(sorted(Counter(t).values())))
            if key not in examples or sz < examples[key][0]:
                examples[key] = (sz, n, t)
    for key in sorted(examples):
        sz, n, t = examples[key]
        print(f"  k={key[0]} multiplicities={key[1]}: size={sz:>3}  e.g. n={n} t={t}")

    overall_min = min(v[0] for v in examples.values())
    print(f"\n  => smallest orbit size that occurs for n>0: {overall_min}")
    print(f"     hence numTypes(n) <= r_4(n) / {overall_min} is VALID but not tight.")

    # Tightness check of numTypes(n) <= r_4(n)/8 :
    bad = [(n, len(types(n)), r4_bruteforce(n))
           for n in range(1, NMAX + 1)
           if len(types(n)) * 8 > r4_bruteforce(n)]
    print(f"\n  counterexamples to numTypes(n) <= r_4(n)/8 : {bad if bad else 'NONE'}")

    print("\nALL CHECKS PASSED.")


if __name__ == "__main__":
    main()
