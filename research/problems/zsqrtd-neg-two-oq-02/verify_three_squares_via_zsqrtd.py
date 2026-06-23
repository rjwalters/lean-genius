#!/usr/bin/env python3
"""
Durable exact verifier for zsqrtd-neg-two-oq-02 (ORIENT, S1).

The slug asks to formalize the Legendre-Gauss three-square theorem
    n = a^2 + b^2 + c^2  (a,b,c in Z)   <=>   n is NOT of the form 4^a (8b+7)
"via the gallery's Z[sqrt(-2)] infrastructure" (norm form x^2 + 2 y^2).

GALLERY STATE (audited): proofs/Proofs/ThreeSquares.lean proves the theorem
`legendre_three_squares` (line 1672), but its converse half is the bare AXIOM
`not_excluded_form_is_sum_three_sq` (line 1665). The forward obstruction and all
descent lemmas (4^a descent `sum_three_sq_iff_four_mul`, square-factor descent
`sum_three_sq_of_sq_mul`) are fully PROVEN. The real deliverable for this slug is
therefore: ELIMINATE that axiom. The parent ZsqrtdNegTwo.lean contributes the
prime case p == 3 (mod 8): p = a^2 + 2 b^2  (split in Z[sqrt(-2)]).

This script verifies, with EXACT integer arithmetic:
  C1  the full iff  (3-squares <=> not excluded), n <= N;
  C2  the Z[sqrt(-2)] BRIDGE: x^2+2y^2 = x^2+y^2+y^2, so any n = x^2+2y^2 is a
      sum of three squares; and the prime mechanism that the parent + Fermat give:
        - p == 1 (mod 4):  p = a^2 + b^2          (Fermat) -> a^2+b^2+0^2;
        - p == 3 (mod 8):  p = a^2 + 2 b^2        (parent) -> a^2+b^2+b^2;
        - p == 7 (mod 8):  excluded (a=0), not needed;
      so EVERY prime that is not excluded is a sum of three squares;
  C3  the CRITICAL LIMITATION (verify-before-assert): three-squares is NOT
      multiplicative, and the binary norm form x^2+2y^2 does NOT represent every
      non-excluded n. There exist squarefree, non-excluded, COMPOSITE n that are
      sums of three squares but are NOT of the form x^2+2y^2 -- so the Z[sqrt(-2)]
      route handles only the prime sub-cases; the full converse for composite
      squarefree n needs the deeper Dirichlet / ternary-form input.
  C4  the descent reductions used by ThreeSquares.lean are sound:
      n is 3-squares  <=>  4n is;  and  k^2 * m 3-squares if m is.

No Lean, no Docker; all checks exact.
"""

import math
from sympy import isprime, factorint


def is_excluded(n: int) -> bool:
    """n = 4^a (8b+7) for some a>=0, b>=0."""
    if n <= 0:
        return False
    while n % 4 == 0:
        n //= 4
    return n % 8 == 7


def three_squares(n: int):
    """Return (a,b,c) with a^2+b^2+c^2=n if it exists, else None. Exact."""
    a = 0
    while a * a <= n:
        r = n - a * a
        b = a
        while b * b <= r:
            c2 = r - b * b
            c = math.isqrt(c2)
            if c >= b and c * c == c2:
                return (a, b, c)
            b += 1
        a += 1
    return None


def is_three_squares(n: int) -> bool:
    return three_squares(n) is not None


def two_squares(n: int):
    """(a,b) with a^2+b^2=n if exists, else None."""
    a = 0
    while a * a <= n:
        r = n - a * a
        b = math.isqrt(r)
        if b >= a and b * b == r:
            return (a, b)
        a += 1
    return None


def repr_x2_2y2(n: int):
    """(x,y) with x^2+2y^2=n if exists, else None."""
    y = 0
    while 2 * y * y <= n:
        r = n - 2 * y * y
        x = math.isqrt(r)
        if x * x == r:
            return (x, y)
        y += 1
    return None


def squarefree(n: int) -> bool:
    return all(e == 1 for e in factorint(n).values()) if n > 1 else (n == 1)


def main():
    N = 20000
    fails = []

    # C1: the full iff.
    bad = 0
    for n in range(1, N + 1):
        if is_three_squares(n) == is_excluded(n):
            bad += 1
            if len(fails) < 20:
                fails.append(("C1", n, is_three_squares(n), is_excluded(n)))
    print(f"C1  3-squares(n) <=> not excluded(n), n in [1,{N}]: "
          f"{'PASS' if bad == 0 else f'FAIL ({bad})'}")

    # C2: Z[sqrt(-2)] bridge + prime mechanism.
    # (a) algebraic bridge x^2+2y^2 = x^2+y^2+y^2 for all x,y.
    bridge = all((x * x + 2 * y * y) == (x * x + y * y + y * y)
                 for x in range(0, 60) for y in range(0, 60))
    # (b) every non-excluded prime is a sum of three squares, via the stated route.
    c2_route = True
    for p in range(2, N + 1):
        if not isprime(p) or is_excluded(p):
            continue
        if p % 4 == 1:                      # Fermat two-square -> three squares
            ok = two_squares(p) is not None
        elif p % 8 == 3:                    # parent: p = x^2 + 2y^2 -> three squares
            ok = repr_x2_2y2(p) is not None
        elif p == 2:
            ok = is_three_squares(p)
        else:                               # p % 8 == 7 would be excluded; p%8 in {?}
            ok = is_three_squares(p)        # any leftover class: must still hold
        if not (ok and is_three_squares(p)):
            c2_route = False
            fails.append(("C2", p, p % 8))
    print(f"C2  bridge x^2+2y^2=x^2+y^2+y^2: {bridge}; "
          f"every non-excluded prime is 3-squares via stated route: "
          f"{'PASS' if c2_route else 'FAIL'}")

    # C3: the limitation -- composite squarefree non-excluded n NOT of form x^2+2y^2.
    witnesses = []
    for n in range(2, 2000):
        if (squarefree(n) and not is_excluded(n) and not isprime(n)
                and is_three_squares(n) and repr_x2_2y2(n) is None):
            witnesses.append(n)
    print(f"C3  composite squarefree non-excluded n that ARE 3-squares but NOT "
          f"x^2+2y^2 (so the binary norm form alone is insufficient): "
          f"{len(witnesses)} found; first 12: {witnesses[:12]}")
    # also: fraction of non-excluded n in range that are x^2+2y^2 representable
    ne = [n for n in range(1, 2000) if not is_excluded(n)]
    covered = [n for n in ne if repr_x2_2y2(n) is not None]
    print(f"    only {len(covered)}/{len(ne)} = {len(covered)/len(ne):.1%} of "
          f"non-excluded n<2000 are x^2+2y^2 -> norm form covers a minority")

    # C4: descent reductions (as used in ThreeSquares.lean) are sound.
    c4 = True
    for n in range(1, 4000):
        if is_three_squares(n) != is_three_squares(4 * n):       # 4n iff n
            c4 = False; fails.append(("C4-4n", n))
        for k in (2, 3):                                          # k^2 m => m direction
            if is_three_squares(n) and not is_three_squares(k * k * n):
                c4 = False; fails.append(("C4-k2", n, k))
    print(f"C4  descent: 3-squares(4n) <=> 3-squares(n) and k^2*n keeps it: "
          f"{'PASS' if c4 else 'FAIL'}")

    ok = (bad == 0) and bridge and c2_route and len(witnesses) > 0 and c4
    print("\n" + ("ALL CHECKS PASS" if ok else f"FAILURES: {fails[:8]}"))
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
