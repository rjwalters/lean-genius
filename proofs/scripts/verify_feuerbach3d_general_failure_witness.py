#!/usr/bin/env python3
"""
Explicit non-orthocentric witness for the axiom `feuerbach_3d_fails_general`
in proofs/Proofs/FeuerbachsTheoremOQ02.lean.

The axiom (currently UNPROVED) states:

    ∃ T : Tetrahedron,
        dot3 (vec3 T.A T.B) (vec3 T.C T.D) ≠ 0  ∧
        ¬ spheresInternallyTangent
              T.twentyFourPointCenter T.incenter
              T.twentyFourPointRadius   T.inradius

i.e. there is a NON-orthocentric tetrahedron (opposite edges AB, CD not
perpendicular) whose twenty-four-point sphere (center N₂₄ = midpoint(O, M),
radius R/3) is NOT internally tangent to the insphere.

Why a fresh witness is needed.  The slug's prior refutations all live at the
*trirectangular* corner tetrahedron T0 = ((2,0,0),(0,3,0),(0,0,6),(0,0,0)) and
the regular tetrahedron — both of which are ORTHOCENTRIC (all opposite edges
perpendicular, so dot3(AB,CD)=0).  Those points satisfy the *negation* of the
first conjunct and therefore CANNOT discharge this existence axiom.  This script
supplies an explicit non-orthocentric witness and certifies BOTH conjuncts in
exact arithmetic, using definitions transcribed verbatim from
FeuerbachsTheoremOQ02.lean.

Witness:  T1 = A=(0,0,0), B=(1,0,0), C=(0,1,0), D=(1,1,1).

Result (exact):
  - nondegenerate: signedVolume6 = 1 ≠ 0.
  - dot3(AB,CD) = 1 ≠ 0   (non-orthocentric → first conjunct holds).
  - circumradius R = √3/2,  inradius r = 1/(1+√3+2√2).
  - dist(N₂₄, I) = (exact surd) ≈ 0.20251,  |R/3 − r| ≈ 0.10883.
  - dist(N₂₄, I) ≠ |R/3 − r|  (gap ≈ 0.0937 > 0) → second conjunct holds.

So T1 witnesses `feuerbach_3d_fails_general`.  A future Docker-enabled session
can replace the `axiom` with `theorem … := ⟨T1, …⟩` and discharge the two
inequalities (separating rational q ≈ 0.15 isolates the non-tangency).

Run:  python3 verify_feuerbach3d_general_failure_witness.py
Requires: sympy (exact surds). Falls back to nothing — sympy is required.
"""

import sympy as sp


def cross(u, v):
    return (u[1] * v[2] - u[2] * v[1],
            u[2] * v[0] - u[0] * v[2],
            u[0] * v[1] - u[1] * v[0])


def dot(u, v):
    return u[0] * v[0] + u[1] * v[1] + u[2] * v[2]


def vec3(P, Q):  # vec3 P Q := Q - P   (matches the Lean def)
    return (Q[0] - P[0], Q[1] - P[1], Q[2] - P[2])


def dist3(P, Q):
    d = vec3(P, Q)
    return sp.sqrt(dot(d, d))


def face_area(P, Q, R):
    # Lean: faceArea uses two edges from a shared vertex, n = cross, sqrt(n·n)/2
    n = cross(vec3(P, Q), vec3(P, R))
    return sp.sqrt(dot(n, n)) / 2


def analyze(A, B, C, D, name):
    A = tuple(sp.Integer(x) for x in A)
    B = tuple(sp.Integer(x) for x in B)
    C = tuple(sp.Integer(x) for x in C)
    D = tuple(sp.Integer(x) for x in D)

    u, v, w = vec3(A, B), vec3(A, C), vec3(A, D)
    det = dot(u, cross(v, w))                       # signedVolume6
    ab_cd = dot(vec3(A, B), vec3(C, D))             # dot3(vec3 A B)(vec3 C D)

    # face areas (A opposite BCD, B opposite ACD, C opposite ABD, D opposite ABC)
    sA = face_area(B, C, D)
    sB = face_area(A, C, D)
    sC = face_area(A, B, D)
    sD = face_area(A, B, C)
    total = sA + sB + sC + sD

    incenter = tuple(sp.simplify(
        (sA * A[i] + sB * B[i] + sC * C[i] + sD * D[i]) / total) for i in range(3))
    volume = sp.Abs(det) / 6
    inradius = sp.simplify(3 * volume / total)

    # circumcenter via Cramer (verbatim from the Lean def)
    vw, wu, uv = cross(v, w), cross(w, u), cross(u, v)
    uu, vv, ww = dot(u, u), dot(v, v), dot(w, w)
    s = sp.Rational(1, 1) / (2 * det)
    O = tuple(sp.simplify(A[i] + s * (uu * vw[i] + vv * wu[i] + ww * uv[i]))
              for i in range(3))
    R = sp.simplify(dist3(O, A))                    # circumradius

    G = tuple(sp.Rational(1, 4) * (A[i] + B[i] + C[i] + D[i]) for i in range(3))
    M = tuple(4 * G[i] - 3 * O[i] for i in range(3))            # mongePoint
    N24 = tuple((O[i] + M[i]) / 2 for i in range(3))           # midpoint(O, M)
    R3 = R / 3                                                  # radius R/3

    dist_NI = sp.simplify(dist3(N24, incenter))
    rhs = sp.Abs(R3 - inradius)
    gap = sp.simplify(dist_NI - rhs)
    is_tangent = (sp.simplify(gap) == 0)

    print(f"=== {name} ===")
    print(f"  A={A} B={B} C={C} D={D}")
    print(f"  signedVolume6 = {det}  (nondegenerate: {det != 0})")
    print(f"  dot3(AB,CD)   = {ab_cd}  (non-orthocentric: {ab_cd != 0})")
    print(f"  circumradius R = {R}")
    print(f"  inradius     r = {inradius}  (~ {sp.N(inradius, 9)})")
    print(f"  dist(N24, I)   = {sp.N(dist_NI, 9)}")
    print(f"  |R/3 - r|      = {sp.N(rhs, 9)}")
    print(f"  gap            = {sp.N(gap, 9)}  (exact-zero: {is_tangent})")
    witnesses = (ab_cd != 0) and (not is_tangent)
    print(f"  WITNESSES feuerbach_3d_fails_general: {witnesses}")
    print()
    return witnesses


def main():
    print("=" * 68)
    print("Witness for axiom feuerbach_3d_fails_general (FeuerbachsTheoremOQ02)")
    print("=" * 68)
    # The witness: non-orthocentric, non-tangent.
    w1 = analyze((0, 0, 0), (1, 0, 0), (0, 1, 0), (1, 1, 1),
                 "T1  (non-orthocentric WITNESS)")
    # Controls: orthocentric tetrahedra have dot3(AB,CD)=0, so they CANNOT
    # witness this axiom regardless of tangency.
    c0 = analyze((2, 0, 0), (0, 3, 0), (0, 0, 6), (0, 0, 0),
                 "T0  (slug's trirectangular control: dot3(AB,CD)=0)")
    c1 = analyze((0, 0, 0), (1, 0, 0), (0, 1, 0), (0, 0, 1),
                 "T0' (unit corner control: dot3(AB,CD)=0)")

    print("-" * 68)
    ok = w1 and (not c0) and (not c1)
    print(f"  WITNESS T1 valid:                 {w1}")
    print(f"  control T0  correctly NOT witness: {not c0}")
    print(f"  control T0' correctly NOT witness: {not c1}")
    print("-" * 68)
    print("ALL CHECKS PASS" if ok else "SOME CHECKS FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
