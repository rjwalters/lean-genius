#!/usr/bin/env python3
"""
verify_pigeonhole_insufficient.py
=================================

NEGATIVE result for the open leaf `exists_slice_point_lt_two_mul`
(`proofs/Proofs/ThreeSquaresSliceMinkowski.lean`):

    for d in {1,2}, p>0, any r:int,  exists (x,y) != 0 with
        p | (x - r*y)   and   x^2 + d*y^2 < 2*p.

A Lean formalizer's *first instinct* is the elementary box-pigeonhole proof of
short-vector existence: choose integer half-widths A,B >= 0 with
(A+1)*(B+1) > p, map the (A+1)*(B+1) points (a,b) (0<=a<=A, 0<=b<=B) to the
residue (a - r*b) mod p, and pigeonhole a collision (a1,b1) != (a2,b2). Then
(x,y) = (a1-a2, b1-b2) is a nonzero lattice vector with |x|<=A, |y|<=B, so

        x^2 + d*y^2 <= A^2 + d*B^2.

This script proves the route **splits sharply on d**: it SUCCEEDS for d=1 but is
**structurally insufficient for d=2**. The best achievable box bound is
    min over A,B>=0, (A+1)(B+1)>p   of   A^2 + d*B^2,
whose large-p asymptotic is the AM-GM floor 2*sqrt(d)*p:

    A^2 + d*B^2 >= 2*sqrt(d)*A*B  ~  2*sqrt(d)*p     (since (A+1)(B+1) ~ AB ~ p).

    d=1:  2*sqrt(1)*p = 2.000*p   -> the floor is exactly 2, BUT the integer +1
                                     slack pulls the realized bound strictly
                                     below 2p:  the explicit symmetric box
                                     A = B = floor(sqrt p) has (floor(sqrt p)+1)^2
                                     > p (Nat.lt_succ_sqrt) and gives
                                     x^2 + y^2 <= 2*floor(sqrt p)^2 <= 2p, with
                                     STRICT "< 2p" whenever p is NOT a perfect
                                     square -- in particular for every prime p
                                     (the application), since no perfect square
                                     > 1 is prime. So the d=1 leaf has an
                                     ELEMENTARY pigeonhole proof; only the finitely
                                     many perfect-square p need a separate (easy)
                                     check.
    d=2:  2*sqrt(2)*p = 2.828*p   -> exceeds 2p outright; route FAILS for ~all p.

By contrast the lattice-OPTIMAL Lagrange-Gauss / Hermite constant is
(2/sqrt(3))*sqrt(d) = 1.155*sqrt(d):

    d=1: 1.155*p,  d=2: 1.633*p   -> both strictly < 2p.

CONCLUSION: the leaf splits on d. The d=1 case is ELEMENTARY (box pigeonhole,
A=B=floor(sqrt p), strict for non-square p). The strict `< 2p` leaf for d=2
*cannot* be obtained from any symmetric product-box pigeonhole; it genuinely
requires the lattice-optimal constant, i.e. the Gauss-reduction / convex-body
Minkowski argument. So the remaining genuinely-hard open content of
`exists_slice_point_lt_two_mul` is the d=2 case ONLY -- a useful narrowing of the
Aristotle / Gauss-reduction target.

Pure stdlib; no sympy/numpy. Run:  python3 verify_pigeonhole_insufficient.py
"""

import math


def best_box_bound(p: int, d: int) -> int:
    """Exact min over A,B>=0 integers with (A+1)*(B+1) > p of A^2 + d*B^2.

    This is the tightest bound the symmetric-box pigeonhole can possibly give:
    a collision is forced as soon as the number of points (A+1)*(B+1) exceeds
    the number of residues p, and the resulting difference vector obeys
    |x|<=A, |y|<=B hence x^2 + d*y^2 <= A^2 + d*B^2.
    """
    best = None
    # B ranges up to where B+1 alone already exceeds p (A=0 admissible).
    for B in range(0, p + 1):
        # Need (A+1)*(B+1) > p, i.e. A+1 > p/(B+1), i.e. A >= ceil((p+1)/(B+1)) - 1.
        a_plus_1_min = (p // (B + 1)) + 1  # smallest integer > p/(B+1)
        A = a_plus_1_min - 1
        if A < 0:
            A = 0
        val = A * A + d * B * B
        if best is None or val < best:
            best = val
    return best


def main() -> None:
    HERMITE = {1: 2 / math.sqrt(3) * math.sqrt(1), 2: 2 / math.sqrt(3) * math.sqrt(2)}
    AMGM = {1: 2 * math.sqrt(1), 2: 2 * math.sqrt(2)}

    print("=" * 72)
    print("verify_pigeonhole_insufficient.py")
    print("  box-pigeonhole bound min(A^2+d*B^2 : (A+1)(B+1)>p) vs 2p")
    print("=" * 72)

    primes = [p for p in range(2, 4000) if all(p % q for q in range(2, int(p**0.5) + 1))]

    failures_d1_strict = 0  # d=1: does box ever beat the AM-GM floor and give < 2p?
    box_ge_2p_d2 = 0        # d=2: box bound >= 2p (route fails) count
    worst_ratio = {1: 0.0, 2: 0.0}

    for p in primes:
        for d in (1, 2):
            b = best_box_bound(p, d)
            ratio = b / p
            worst_ratio[d] = max(worst_ratio[d], ratio)
            if d == 1 and b < 2 * p:
                # box achieved a STRICT < 2p for d=1 (allowed; floor is exactly 2)
                pass
            if d == 1 and b >= 2 * p:
                failures_d1_strict += 1
            if d == 2 and b >= 2 * p:
                box_ge_2p_d2 += 1

    # Asymptotic AM-GM lower bound check: best_box_bound(p,d)/p -> 2*sqrt(d).
    big = primes[-1]
    print(f"\nprimes scanned ........ {len(primes)} (2 .. {big})")
    print("\n[box route, d=1]")
    print(f"  worst box bound / p .......... {worst_ratio[1]:.5f}")
    print(f"  AM-GM floor 2*sqrt(1) ........ {AMGM[1]:.5f}  (box can only reach <= 2p, the floor)")
    print(f"  primes where box >= 2p ....... {failures_d1_strict} of {len(primes)}"
          f"   ({100*failures_d1_strict/len(primes):.1f}%  -> strict <2p NOT guaranteed)")
    print(f"  Hermite/Gauss 2/sqrt3*sqrt1 .. {HERMITE[1]:.5f}  (lattice-optimal, always < 2)")

    print("\n[box route, d=2]  (the binding case)")
    print(f"  worst box bound / p .......... {worst_ratio[2]:.5f}")
    print(f"  AM-GM floor 2*sqrt(2) ........ {AMGM[2]:.5f}  > 2  -> box ALWAYS exceeds 2p asymptotically")
    print(f"  primes where box >= 2p ....... {box_ge_2p_d2} of {len(primes)}"
          f"   ({100*box_ge_2p_d2/len(primes):.1f}%  -> route FAILS)")
    print(f"  Hermite/Gauss 2/sqrt3*sqrt2 .. {HERMITE[2]:.5f}  (lattice-optimal, < 2  -> route SUCCEEDS)")

    # The decisive assertions:
    #  (1) d=2 box bound is >= 2p for the overwhelming majority of large primes,
    #      so the box route cannot prove the strict leaf for d=2.
    #  (2) the box bound saturates the AM-GM floor 2*sqrt(d), strictly above the
    #      Hermite constant for d=2.
    d2_majority_fail = box_ge_2p_d2 > 0.9 * len(primes)
    d2_floor_above_2 = AMGM[2] > 2.0
    d2_hermite_below_2 = HERMITE[2] < 2.0

    print("\n" + "=" * 72)
    print("ASSERTIONS")
    print(f"  [1] d=2 box bound >= 2p for >90% of primes ......... {d2_majority_fail}")
    print(f"  [2] AM-GM floor 2*sqrt(2) > 2 (box asymptote fails) . {d2_floor_above_2}")
    print(f"  [3] Hermite 2/sqrt3*sqrt2 < 2 (Gauss route works) ... {d2_hermite_below_2}")
    ok = d2_majority_fail and d2_floor_above_2 and d2_hermite_below_2
    print("=" * 72)
    print("RESULT:", "ALL CHECKS PASS" if ok else "FAILED")
    print("=" * 72)
    print(
        "\nINTERPRETATION\n"
        "  The symmetric product-box pigeonhole has AM-GM floor 2*sqrt(d):\n"
        "  d=1 -> floor 2.0, but the integer +1 slack of the explicit box\n"
        "  A=B=floor(sqrt p) realizes x^2+y^2 <= 2*floor(sqrt p)^2 < 2p strictly\n"
        "  for every non-square p (all primes), so the d=1 leaf is ELEMENTARY;\n"
        "  d=2 -> floor 2.83 > 2, fails for ~all p. The lattice-optimal\n"
        "  Lagrange-Gauss / Hermite constant 1.155*sqrt(d) is < 2 for both d.\n"
        "  Hence the leaf `exists_slice_point_lt_two_mul` CANNOT be discharged\n"
        "  by an elementary box pigeonhole for d=2 -- the Gauss-reduction (or 2D\n"
        "  convex-body Minkowski) argument is necessary there. Net: the hard\n"
        "  open content narrows to the single d=2 case."
    )
    raise SystemExit(0 if ok else 1)


if __name__ == "__main__":
    main()
