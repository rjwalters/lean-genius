#!/usr/bin/env python3
"""
Exact integer search for primitive Fermat defect-one witnesses, both signs.

OQ-02 (Level 3): for every n >= 3 and every epsilon in {-1,+1}, does there
exist a primitive nontrivial triple (a,b,c) with

    2 <= a <= b < c,  gcd(a,b,c) = 1,  a^n + b^n - c^n = epsilon ?

On Nat this splits into
    negative defect (eps = -1):  a^n + b^n + 1 = c^n   (c^n = s + 1)
    positive defect (eps = +1):  a^n + b^n     = c^n + 1 (c^n = s - 1)
with s = a^n + b^n.

The arithmetic is exact (Python big ints). For each (a,b) with 2 <= a <= b,
we test whether s+1 and s-1 are perfect n-th powers c^n with c > b, then
check primitivity. No floating point: integer n-th root by bisection with
exact verification.

This pins down which (n, sign) rows of the conjecture's table are realised by
*small* witnesses, and -- equally informative -- which rows have NO witness
below the searched bound (evidence that any witness, if it exists, is
astronomically large, consistent with abc-style sparsity heuristics).

Usage:  python3 verify_defect_search.py [--bmax B] [--nmax N]
"""

import argparse
from math import gcd


def iroot(x, n):
    """Exact integer n-th root: largest r with r**n <= x (x >= 0)."""
    if x < 0:
        return -1
    if x == 0:
        return 0
    # initial bracket
    hi = 1
    while hi ** n <= x:
        hi <<= 1
    lo = hi >> 1
    while lo < hi:
        mid = (lo + hi + 1) >> 1
        if mid ** n <= x:
            lo = mid
        else:
            hi = mid - 1
    return lo


def is_perfect_power(x, n):
    """Return c if x == c**n with c >= 0, else None."""
    if x < 0:
        return None
    r = iroot(x, n)
    if r ** n == x:
        return r
    return None


def search(n, bmax):
    """Return lists of primitive witnesses (a,b,c) for neg and pos defect."""
    neg = []  # a^n + b^n + 1 = c^n
    pos = []  # a^n + b^n     = c^n + 1
    # precompute powers
    powr = [k ** n for k in range(bmax + 2)]
    for a in range(2, bmax + 1):
        an = powr[a]
        for b in range(a, bmax + 1):
            s = an + powr[b]
            # negative defect: c^n = s + 1
            c = is_perfect_power(s + 1, n)
            if c is not None and c > b:
                if gcd(gcd(a, b), c) == 1:
                    neg.append((a, b, c))
            # positive defect: c^n = s - 1
            c = is_perfect_power(s - 1, n)
            if c is not None and c > b:
                if gcd(gcd(a, b), c) == 1:
                    pos.append((a, b, c))
    return neg, pos


def verify_families(tmax=200):
    """Verify the two parametric n=3 families that settle OQ-02 at n=3.

    These are the Lean `ring`-identities in
    proofs/Proofs/FermatDefectOneFamilies.lean.

      negative defect: (9t^4 - 3t)^3 + (9t^3 - 1)^3 + 1 = (9t^4)^3
      positive defect: (9s^4)^3   + (9s^3 + 1)^3       = (9s^4 + 3s)^3 + 1

    Both descend from Mahler's parametrization of x^3+y^3+z^3=1 at t and -t.
    We check the identity AND primitivity (gcd of the ordered triple = 1) AND
    the witness bounds 2 <= a <= b < c, for every parameter 1..tmax.
    """
    neg_c, pos_c = set(), set()
    for t in range(1, tmax + 1):
        # negative: a3+b3+1=c3
        A, B, c = 9 * t ** 4 - 3 * t, 9 * t ** 3 - 1, 9 * t ** 4
        a, b = sorted((A, B))
        assert a ** 3 + b ** 3 + 1 == c ** 3, f"neg identity fails at t={t}"
        assert gcd(gcd(a, b), c) == 1, f"neg not primitive at t={t}: {(a,b,c)}"
        assert 2 <= a <= b < c, f"neg bounds fail at t={t}: {(a,b,c)}"
        neg_c.add(c)
    for s in range(1, tmax + 1):
        A, B, c = 9 * s ** 4, 9 * s ** 3 + 1, 9 * s ** 4 + 3 * s
        a, b = sorted((A, B))
        assert a ** 3 + b ** 3 == c ** 3 + 1, f"pos identity fails at s={s}"
        assert gcd(gcd(a, b), c) == 1, f"pos not primitive at s={s}: {(a,b,c)}"
        assert 2 <= a <= b < c, f"pos bounds fail at s={s}: {(a,b,c)}"
        pos_c.add(c)
    # strictly increasing c => infinitely many distinct primitive witnesses
    assert len(neg_c) == tmax and len(pos_c) == tmax
    print(f"[families] OK: both n=3 families primitive & in-bounds for "
          f"t,s = 1..{tmax}; {tmax} distinct c each (=> infinitely many).")


def self_test():
    """Confirm the two known n=3 benchmarks are found and families hold."""
    neg, pos = search(3, 12)
    assert (6, 8, 9) in neg, f"missing neg n=3 witness; got {neg}"
    assert (9, 10, 12) in pos, f"missing pos n=3 witness; got {pos}"
    # sanity on iroot
    assert iroot(729, 3) == 9 and iroot(728, 3) == 8
    assert is_perfect_power(1729 - 1, 3) == 12
    print("[self-test] OK: n=3 benchmarks (6,8,9) neg and (9,10,12) pos recovered.")
    verify_families()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--bmax", type=int, default=3000,
                    help="search a,b up to this bound (default 3000)")
    ap.add_argument("--nmax", type=int, default=8,
                    help="search exponents 3..nmax (default 8)")
    args = ap.parse_args()

    self_test()
    print(f"\nSearching primitive defect-one witnesses, 2<=a<=b<={args.bmax}, "
          f"n=3..{args.nmax}\n")
    print(f"{'n':>3} {'#neg(-1)':>9} {'#pos(+1)':>9}  smallest witnesses")
    for n in range(3, args.nmax + 1):
        neg, pos = search(n, args.bmax)
        # smallest by c
        neg_s = sorted(neg, key=lambda t: (t[2], t[0], t[1]))[:2]
        pos_s = sorted(pos, key=lambda t: (t[2], t[0], t[1]))[:2]
        def fmt(lst):
            return ", ".join(f"({a},{b},{c})" for a, b, c in lst) or "NONE"
        print(f"{n:>3} {len(neg):>9} {len(pos):>9}  "
              f"neg=[{fmt(neg_s)}]  pos=[{fmt(pos_s)}]")
    print("\nNote: 'NONE' at the searched bound is evidence of absence of SMALL "
          "witnesses,\nnot a proof of non-existence (abc heuristics permit rare "
          "large witnesses).")


if __name__ == "__main__":
    main()
