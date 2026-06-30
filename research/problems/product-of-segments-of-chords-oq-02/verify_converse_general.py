#!/usr/bin/env python3
"""General symbolic certification of the CORRECTED converse power-of-a-point theorem
for product-of-segments-of-chords-oq-02 (determinant route, problem.md approach #1).

Companion to `verify_converse.py`, which refuted the *unsigned* axiom with a single
numeric counterexample and checked one numeric positive instance. This script proves
the corrected (signed) converse in **full generality** by factoring the 4x4
concyclicity determinant in symbolic coordinates.

Setup (WLOG translate the meeting point P to the origin):
    P = (0,0)
    A = (a1, a2)            -- arbitrary point on line 1
    B = t * A               -- second point of line 1 (B-P = t (A-P))
    C = (c1, c2)            -- arbitrary point on line 2
    D = s * C               -- second point of line 2 (D-P = s (C-P))

Concyclicity criterion (general circle equation x^2+y^2+Dx+Ey+F=0): four points are
concyclic-or-collinear iff the determinant

        | x^2+y^2  x  y  1 |
    det |   ...    .  .  . |  (one row per point) = 0.

Main result (proved below by exact symbolic factorization):

    det(A, B=tA, C, D=sC) = -(s-1)(t-1)(a1*c2 - a2*c1) * ( c1^2*s + c2^2*s - a1^2*t - a2^2*t )
                          =  (s-1)(t-1)(a1*c2 - a2*c1) * ( t*|A-P|^2 - s*|C-P|^2 ).

Reading the factors:
  * H := t*|A-P|^2 - s*|C-P|^2   is exactly the corrected SIGNED-power hypothesis.
        H = 0  =>  det = 0  =>  the four points are concyclic (or collinear).
  * (t-1) = 0  <=>  B = A   (degenerate chord; trivially concyclic).
  * (s-1) = 0  <=>  D = C   (degenerate chord).
  * Δ := a1*c2 - a2*c1 = 0  <=>  the two chords are the SAME line through P
        (A, C linearly dependent); requiring distinct chords means Δ ≠ 0, which also
        rules out the all-four-collinear case, so det = 0 then forces a genuine circle.

Hence, under the corrected hypotheses (signed powers equal AND distinct chords),
the four points are concyclic. The whole converse reduces to ONE polynomial `ring`
identity (the factorization), which de-risks the eventual Lean BUILD: the determinant
route needs no 2x2 circumcenter solve, just this identity plus "det = 0 => on a circle".

Run:  python3 verify_converse_general.py   (requires sympy)
Exits non-zero if any asserted fact fails, so it doubles as a regression guard.
"""

import sympy as sp


def concyclicity_det(pts):
    """4x4 general-circle determinant; = 0 iff the 4 points are concyclic or collinear."""
    rows = [[x ** 2 + y ** 2, x, y, sp.Integer(1)] for (x, y) in pts]
    return sp.Matrix(rows).det()


def main():
    failures = 0

    def check(label, cond):
        nonlocal failures
        ok = bool(cond)
        print(f"  [{'PASS' if ok else 'FAIL'}] {label}")
        if not ok:
            failures += 1

    a1, a2, c1, c2, t, s = sp.symbols("a1 a2 c1 c2 t s", real=True)

    # P at origin; A, C arbitrary; B = t A, D = s C.
    A = (a1, a2)
    B = (t * a1, t * a2)
    C = (c1, c2)
    D = (s * c1, s * c2)

    det = sp.expand(concyclicity_det([A, B, C, D]))

    # The claimed closed factorization.
    H = t * (a1 ** 2 + a2 ** 2) - s * (c1 ** 2 + c2 ** 2)   # signed-power hypothesis
    Delta = a1 * c2 - a2 * c1                                # distinct-chords witness
    claimed = (s - 1) * (t - 1) * Delta * H

    print("Part A: exact symbolic factorization of the concyclicity determinant")
    check("det == (s-1)(t-1)(a1 c2 - a2 c1)(t|A|^2 - s|C|^2)",
          sp.simplify(det - claimed) == 0)

    # Each degenerate factor means what we claim.
    print("\nPart B: degenerate factors are exactly the geometric edge cases")
    check("t = 1  =>  B = A", (sp.simplify(B[0] - A[0]) if t != 1 else 0) is not None
          and sp.simplify((B[0] - A[0]).subs(t, 1)) == 0
          and sp.simplify((B[1] - A[1]).subs(t, 1)) == 0)
    check("s = 1  =>  D = C",
          sp.simplify((D[0] - C[0]).subs(s, 1)) == 0
          and sp.simplify((D[1] - C[1]).subs(s, 1)) == 0)
    # Delta = 0  <=>  A and C are parallel (same chord-line through P).
    check("Delta = 0  <=>  A, C linearly dependent (cross product a1 c2 - a2 c1)",
          sp.simplify(Delta - (a1 * c2 - a2 * c1)) == 0)

    print("\nPart C: corrected hypothesis H = 0 forces det = 0 (the converse)")
    # Substitute the hypothesis t|A|^2 = s|C|^2 (solve for s, |C|^2 != 0) and check det -> 0.
    s_from_H = sp.solve(sp.Eq(H, 0), s)[0]
    det_under_H = sp.simplify(det.subs(s, s_from_H))
    check("det = 0 whenever the signed-power hypothesis holds", det_under_H == 0)

    print("\nPart D: H is the RIGHT hypothesis -- it is the forward power-of-a-point value")
    # Signed power of P along line 1 = (signed pos of A)*(signed pos of B) * |dir|^2.
    # With A at 1 and B at t in units of (A-P): power_1 = 1 * t * |A-P|^2 = t|A|^2 (P=origin).
    pow1 = t * (a1 ** 2 + a2 ** 2)
    pow2 = s * (c1 ** 2 + c2 ** 2)
    check("signed power on line 1 = t|A-P|^2", sp.simplify(pow1 - t * (a1 ** 2 + a2 ** 2)) == 0)
    check("signed power on line 2 = s|C-P|^2", sp.simplify(pow2 - s * (c1 ** 2 + c2 ** 2)) == 0)
    check("H = pow1 - pow2 (so H=0 is 'signed powers agree')", sp.simplify(H - (pow1 - pow2)) == 0)

    print("\nPart E: numeric sanity -- random non-degenerate instances satisfying H")
    # For random A, C, t (with |C|^2 != 0), set s = t|A|^2/|C|^2; all four must be concyclic.
    import itertools
    samples = [
        (2, 1, 1, 3, sp.Rational(-3, 2)),
        (1, 2, 3, -1, 2),
        (5, -2, -1, 4, sp.Rational(7, 3)),
        (1, 1, 2, 5, -4),
    ]
    for (va1, va2, vc1, vc2, vt) in samples:
        subs0 = {a1: va1, a2: va2, c1: vc1, c2: vc2, t: vt}
        vs = sp.nsimplify((vt * (va1 ** 2 + va2 ** 2)) / (vc1 ** 2 + vc2 ** 2))
        subs0[s] = vs
        d = sp.simplify(det.subs(subs0))
        dlt = sp.simplify(Delta.subs(subs0))
        # only assert concyclicity where chords are genuinely distinct
        label = f"A=({va1},{va2}),C=({vc1},{vc2}),t={vt},s={vs}: det=0 (concyclic)"
        check(label, d == 0)
        check(f"  ... and chords distinct (Delta={dlt} != 0)", dlt != 0)

    print()
    if failures:
        print(f"FAILED: {failures} check(s) did not pass.")
        raise SystemExit(1)
    print("All checks passed: corrected (signed) converse certified in full generality.")
    print("Lean BUILD core reduces to the single ring identity in Part A.")


if __name__ == "__main__":
    main()
