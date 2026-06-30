#!/usr/bin/env python3
"""Reproducible verification for product-of-segments-of-chords-oq-02.

Independently checks (with exact symbolic arithmetic) the integrity finding
documented in knowledge.md: the gallery axiom
`converse_product_implies_concyclic_axiom` in
proofs/Proofs/ProductOfSegmentsOfChords.lean is FALSE as stated because it uses
*unsigned* segment products `‖P-A‖·‖P-B‖ = ‖P-C‖·‖P-D‖`, whereas the true
converse of power-of-a-point requires *signed* products to agree.

Run:  python3 verify_converse.py   (requires sympy)

Exits non-zero if any asserted fact fails, so it doubles as a regression guard.
"""

import sympy as sp


def vsub(X, Y):
    return (X[0] - Y[0], X[1] - Y[1])


def norm2(V):
    return V[0] ** 2 + V[1] ** 2


def nrm(V):
    return sp.sqrt(norm2(V))


def circle_through(A, B, C):
    """Coefficients (D,E,F) of x^2+y^2+Dx+Ey+F=0 through three points."""
    D, E, F = sp.symbols("D E F")
    eqs = [sp.Eq(x ** 2 + y ** 2 + D * x + E * y + F, 0) for (x, y) in (A, B, C)]
    sol = sp.solve(eqs, [D, E, F], dict=True)
    return sol[0] if sol else None


def eval_circle(P, coef):
    D, E, F = sp.symbols("D E F")
    x, y = P
    return sp.simplify((x ** 2 + y ** 2 + D * x + E * y + F).subs(coef))


def scalar_ratio_x(P, A, X):
    """t with X - P = t (A - P), reading the x-component (A,X collinear via P)."""
    return sp.nsimplify((X[0] - P[0]) / (A[0] - P[0]))


def scalar_ratio_y(P, C, X):
    return sp.nsimplify((X[1] - P[1]) / (C[1] - P[1]))


def main():
    failures = 0

    def check(label, cond):
        nonlocal failures
        ok = bool(cond)
        print(f"  [{'PASS' if ok else 'FAIL'}] {label}")
        if not ok:
            failures += 1

    # ------------------------------------------------------------------
    # Part 1 — the counterexample that refutes the unsigned axiom.
    #   P=(0,0); A=(1,0),B=(-4,0) on the x-axis; C=(0,1),D=(0,4) on the y-axis.
    # ------------------------------------------------------------------
    print("Part 1: counterexample to the unsigned converse")
    P = (sp.Integer(0), sp.Integer(0))
    A = (sp.Integer(1), sp.Integer(0))
    B = (sp.Integer(-4), sp.Integer(0))
    C = (sp.Integer(0), sp.Integer(1))
    D = (sp.Integer(0), sp.Integer(4))

    # collinearity scalars: B-P = t(A-P), D-P = s(C-P)
    t = scalar_ratio_x(P, A, B)
    s = scalar_ratio_y(P, C, D)
    check("B-P = t(A-P) with t = -4", t == -4)
    check("D-P = s(C-P) with s = 4", s == 4)
    check("scalar form reproduces B", (P[0] + t * (A[0] - P[0]), P[1] + t * (A[1] - P[1])) == B)
    check("scalar form reproduces D", (P[0] + s * (C[0] - P[0]), P[1] + s * (C[1] - P[1])) == D)

    # all four points distinct from P, and A!=B, C!=D
    check("A,B,C,D all != P", all(Q != P for Q in (A, B, C, D)))
    check("A != B and C != D", A != B and C != D)

    # the axiom's UNSIGNED hypothesis holds
    pa = nrm(vsub(P, A)) * nrm(vsub(P, B))
    pc = nrm(vsub(P, C)) * nrm(vsub(P, D))
    check("unsigned ‖P-A‖·‖P-B‖ = 4", sp.simplify(pa) == 4)
    check("unsigned ‖P-C‖·‖P-D‖ = 4", sp.simplify(pc) == 4)
    check("UNSIGNED hypothesis satisfied (4 = 4)", sp.simplify(pa - pc) == 0)

    # the SIGNED powers disagree in sign -> no shared circle
    sig_ab = sp.simplify(t * norm2(vsub(A, P)))
    sig_cd = sp.simplify(s * norm2(vsub(C, P)))
    check("signed power on line AB = -4 (P inside chord AB)", sig_ab == -4)
    check("signed power on line CD = +4 (P outside segment CD)", sig_cd == 4)
    check("signed powers have OPPOSITE sign", sig_ab * sig_cd < 0)

    # conclusion fails: D is not on the unique circle through A,B,C
    coef = circle_through(A, B, C)
    check("circle ABC is x^2+y^2+3x+3y-4=0",
          coef == {sp.Symbol("D"): 3, sp.Symbol("E"): 3, sp.Symbol("F"): -4})
    check("D=(0,4) NOT on circle ABC (eval = 24 != 0)", eval_circle(D, coef) != 0)
    print("  => unsigned converse is FALSE: hypotheses hold, conclusion fails.\n")

    # ------------------------------------------------------------------
    # Part 2 — the corrected SIGNED hypothesis rejects the counterexample.
    # ------------------------------------------------------------------
    print("Part 2: corrected signed hypothesis  t·‖A-P‖² = s·‖C-P‖²")
    lhs = t * norm2(vsub(A, P))
    rhs = s * norm2(vsub(C, P))
    check("signed hypothesis is VIOLATED on the counterexample (-4 != 4)",
          sp.simplify(lhs - rhs) != 0)
    print("  => corrected statement correctly excludes the bad instance.\n")

    # ------------------------------------------------------------------
    # Part 3 — positive control: genuinely concyclic data where the
    #   corrected signed hypothesis holds and all four points lie on a circle.
    #   Circle centered at O=(0,0), r²=25; P=(1,1) interior;
    #   horizontal chord y=1 and vertical chord x=1 through P.
    # ------------------------------------------------------------------
    print("Part 3: positive control (corrected hypothesis holds => concyclic)")
    O = (sp.Integer(0), sp.Integer(0))
    r2 = sp.Integer(25)
    Pp = (sp.Integer(1), sp.Integer(1))
    A2 = (sp.sqrt(24), sp.Integer(1))
    B2 = (-sp.sqrt(24), sp.Integer(1))
    C2 = (sp.Integer(1), sp.sqrt(24))
    D2 = (sp.Integer(1), -sp.sqrt(24))

    t2 = sp.simplify((B2[0] - Pp[0]) / (A2[0] - Pp[0]))
    s2 = sp.simplify((D2[1] - Pp[1]) / (C2[1] - Pp[1]))
    sig_a2 = sp.simplify(t2 * norm2(vsub(A2, Pp)))
    sig_c2 = sp.simplify(s2 * norm2(vsub(C2, Pp)))
    check("signed hypothesis HOLDS (both signed powers = -23)",
          sp.simplify(sig_a2 - sig_c2) == 0 and sig_a2 == -23)
    for nm, Pt in [("A", A2), ("B", B2), ("C", C2), ("D", D2)]:
        check(f"{nm} lies on circle (‖·-O‖² = 25)",
              sp.simplify(norm2(vsub(Pt, O)) - r2) == 0)
    print()

    if failures:
        print(f"FAILED: {failures} check(s) did not pass.")
        raise SystemExit(1)
    print("All checks passed.")


if __name__ == "__main__":
    main()
