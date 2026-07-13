#!/usr/bin/env python3
"""
Erdős Problem #493, follow-up OQ-01: exact characterization and representation
count of the product-minus-sum image.

Parent result (Erdos493Problem.lean): k = 2 suffices, i.e. every n >= 0 is
representable as  n = a*b - (a + b)  with a, b >= 2  (one direction only:
n >= 0  =>  representable, via a = 2, b = n + 2).

OQ-01 asks for the EXACT image and the number of representations.

Central identity (the missing converse + the counting bijection):

    a*b - (a + b) = (a - 1)*(b - 1) - 1.

Write u = a - 1, v = b - 1.  Then a, b >= 2  <=>  u, v >= 1, and

    n = a*b - (a + b)   <=>   n + 1 = u * v    with u, v >= 1.

Consequences proved here by exhaustive check:

  (C1) IMAGE.  { a*b - (a+b) : a,b >= 2 } = { n in Z : n >= 0 }.
       In particular every negative integer has NO representation
       (the parent file leaves this converse direction unproved).

  (C2) COUNT.  The number of ORDERED pairs (a, b) with a,b >= 2 and
       a*b - (a+b) = n  equals  tau(n + 1)  = number of positive divisors
       of n + 1  (each divisor u | n+1 gives u = a-1, v = (n+1)/u = b-1).

  (C3) UNORDERED COUNT.  The number of UNORDERED representations {a,b}
       equals ceil(tau(n+1)/2) = number of divisors u of n+1 with
       u <= sqrt(n+1)  (i.e. divisor pairs up to order).

  (C4) UNIQUE-REPRESENTATION CHARACTERIZATION.  n has exactly one ordered
       representation  <=>  tau(n+1) = 1  <=>  n + 1 = 1  <=>  n = 0.
       n has exactly one unordered representation <=> tau(n+1) in {1, 2}
       <=>  n + 1 is 1 or prime.  (A prime square n+1 = p^2 already has TWO
       unordered reps: {1, p^2} from u=1 and {p, p} from u=v=p.)

All assertions below pass (pure arithmetic, no external proof backend).
"""

from math import isqrt
from sympy import divisor_count, isprime


def reps_ordered(n, cap=None):
    """All ordered (a,b), a,b>=2, with a*b-(a+b)=n. Bounded since a-1 | n+1."""
    if n + 1 <= 0:
        # u*v = n+1 <= 0 impossible with u,v >= 1
        return []
    out = []
    m = n + 1
    for u in range(1, m + 1):
        if m % u == 0:
            v = m // u
            out.append((u + 1, v + 1))  # (a, b)
    return out


def brute_reps_ordered(n, bound):
    """Independent brute force over a,b in [2,bound] (no factorization)."""
    return [(a, b) for a in range(2, bound + 1) for b in range(2, bound + 1)
            if a * b - (a + b) == n]


def main():
    ok = True

    # (C1) image is exactly {n >= 0}; negatives unrepresentable
    for n in range(-50, 0):
        if brute_reps_ordered(n, 60):
            print(f"FAIL C1: negative n={n} is representable"); ok = False
    for n in range(0, 60):
        if not brute_reps_ordered(n, n + 4):
            print(f"FAIL C1: nonneg n={n} not representable"); ok = False

    # (C2) ordered count == tau(n+1); cross-check divisor enum vs brute force
    for n in range(0, 300):
        via_div = reps_ordered(n)
        via_brute = brute_reps_ordered(n, n + 4)
        tau = divisor_count(n + 1)
        if len(via_div) != tau:
            print(f"FAIL C2a: n={n} divisor-count {len(via_div)} != tau {tau}"); ok = False
        if sorted(via_div) != sorted(via_brute):
            print(f"FAIL C2b: n={n} divisor enum != brute force"); ok = False

    # (C3) unordered count == #divisors u of n+1 with u <= sqrt(n+1)
    for n in range(0, 300):
        m = n + 1
        small = sum(1 for u in range(1, isqrt(m) + 1) if m % u == 0)
        unordered = {tuple(sorted(p)) for p in reps_ordered(n)}
        if len(unordered) != small:
            print(f"FAIL C3: n={n} unordered {len(unordered)} != small-div {small}")
            ok = False

    # (C4) unique ordered rep <=> n == 0
    uniq_ordered = [n for n in range(0, 300) if len(reps_ordered(n)) == 1]
    if uniq_ordered != [0]:
        print(f"FAIL C4a: unique-ordered set = {uniq_ordered}, expected [0]"); ok = False
    # unique unordered rep <=> n+1 is 1 or prime  (tau in {1,2})
    for n in range(0, 300):
        m = n + 1
        unordered = {tuple(sorted(p)) for p in reps_ordered(n)}
        is_unique = (len(unordered) == 1)
        pred = (m == 1) or isprime(m)
        if is_unique != pred:
            print(f"FAIL C4b: n={n} m={m} uniqueUnordered={is_unique} pred={pred}")
            ok = False

    # spot identity (a-1)(b-1)-1 == ab-(a+b)
    for a in range(2, 40):
        for b in range(2, 40):
            if (a - 1) * (b - 1) - 1 != a * b - (a + b):
                print(f"FAIL identity a={a} b={b}"); ok = False

    print("ALL CHECKS PASS" if ok else "SOME CHECKS FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
