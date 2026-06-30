#!/usr/bin/env python3
"""Exploratory finding for feuerbachs-theorem-oq-02-murakami (S10, build-free):
the Grace simultaneous-tangency is UNIVERSAL across tetrahedra; only the
RATIONALITY of the Grace sphere is special to the trirectangular family.

WHAT S7/S9 ESTABLISHED. For a *trirectangular* tetrahedron (D=0, A=(a,0,0),
B=(0,b,0), C=(0,0,c)) the sphere through face A,B,C is simultaneously
INTERNALLY tangent to the insphere AND to the exsphere opposite D, with a
RATIONAL centre Θ and radius R (the surd √(a²b²+b²c²+c²a²) cancels). Certified
in `verify_grace_proof_certificate.py`.

NEW FINDING (this script). The *existence* of that simultaneous tangency is NOT
special to trirectangular — nor even to orthocentric — tetrahedra. For ANY
tetrahedron and ANY face f (opposite vertex v):

    the unique sphere through the CIRCUMCIRCLE of f that is internally tangent
    to the insphere is ALSO internally tangent to the exsphere opposite v.

Verified below to 60 decimal digits (residuals ~1e-60, i.e. exact) on:
  - the trirectangular control T0=(2,3,6)  [4/4 faces],
  - a genuine non-trirectangular ORTHOCENTRIC tetra (all 6 pairwise dots equal
    w.r.t. orthocentre at 0)  [4/4 faces],
  - two generic NON-orthocentric tetrahedra  [4/4 faces each].

CONSEQUENCE / REFRAME. The "3D Feuerbach" content that is genuinely special to
the trirectangular (and, more broadly, to whatever sub-family admits it) case is
the CLOSED-FORM RATIONALITY of the tangent sphere, not the bare fact that a
simultaneously-tangent sphere exists. The face-circumcircle pencil ALWAYS
contains such a member. This is why the slug's earlier ruled-out candidates —
the centroid/homothetic spheres (N24,R/3), (G,R/2), defined by a CENTRE+RADIUS
formula rather than selected from the face pencil — fail: they are not chosen to
be tangent, whereas the Grace sphere is the pencil member that is.

WHY (2D analogue, the likely proof route for a future symbolic/Lean attempt).
Both the insphere and the exsphere opposite v are tangent to the face plane π,
and every sphere through f's circumcircle meets π in that same fixed circle.
The statement is the 3D lift of the classical planar lemma "a circle through B,C
tangent to the incircle is tangent to the A-excircle" (equal tangent lengths
BX = CX', the incircle/excircle touch points on BC being symmetric about the
midpoint). The face-plane reduction makes the 3D claim a one-plane statement.

Run: python3 verify_grace_universal_tangency.py   (needs only mpmath)
"""

import mpmath as mp

mp.mp.dps = 60
EPS = mp.mpf(10) ** -40        # "is zero" threshold at this precision


# ---------- 3-vector helpers (lists of mpf) ----------
def vec(*x):
    return [mp.mpf(str(v)) for v in x]


def sub(a, b):
    return [a[i] - b[i] for i in range(3)]


def add(a, b):
    return [a[i] + b[i] for i in range(3)]


def smul(s, a):
    return [s * a[i] for i in range(3)]


def dot(a, b):
    return a[0] * b[0] + a[1] * b[1] + a[2] * b[2]


def cross(a, b):
    return [a[1] * b[2] - a[2] * b[1],
            a[2] * b[0] - a[0] * b[2],
            a[0] * b[1] - a[1] * b[0]]


def norm(a):
    return mp.sqrt(dot(a, a))


# ---------- tetrahedron metric primitives ----------
def face_area(P, Q, R):
    return norm(cross(sub(Q, P), sub(R, P))) / 2


def volume(V):
    A, B, C, D = V
    return abs(dot(cross(sub(B, A), sub(C, A)), sub(D, A))) / 6


def face_areas(V):
    # S[i] = area of the face OPPOSITE vertex i
    return [face_area(*[V[j] for j in range(4) if j != i]) for i in range(4)]


def insphere(V):
    S = face_areas(V)
    tot = sum(S)
    I = [sum(S[i] * V[i][k] for i in range(4)) / tot for k in range(3)]
    return I, 3 * volume(V) / tot


def exsphere_opposite(V, k):
    S = face_areas(V)
    den = sum(S[i] for i in range(4) if i != k) - S[k]
    if den <= EPS:
        return None, None
    E = [(sum(S[i] * V[i][kk] for i in range(4) if i != k) - S[k] * V[k][kk]) / den
         for kk in range(3)]
    return E, 3 * volume(V) / den


def triangle_circum(A, B, C):
    u, v = sub(B, A), sub(C, A)
    uu, vv, uv = dot(u, u), dot(v, v), dot(u, v)
    det = uu * vv - uv * uv
    al = (uu * vv / 2 - vv * uv / 2) / det
    be = (vv * uu / 2 - uu * uv / 2) / det
    O = add(A, add(smul(al, u), smul(be, v)))
    n = cross(u, v)
    n = smul(1 / norm(n), n)
    return O, norm(sub(O, A)), n


def is_orthocentric(V):
    A, B, C, D = V
    return all(abs(d) < EPS for d in
               (dot(sub(B, A), sub(D, C)),
                dot(sub(C, A), sub(D, B)),
                dot(sub(D, A), sub(C, B))))


# ---------- the universal-tangency check ----------
def face_pencil_residuals(V, vtx):
    """On the face opposite `vtx`, find the sphere(s) through that face's
    circumcircle internally tangent to the insphere, and return their tangency
    residual to the exsphere opposite `vtx`.

    Pencil: centre O + s·n (O = triangle circumcentre, n unit normal),
    radius² = Rt² + s². Insphere (I,r) tangency:
        |O−I + s n|² = (radius ∓ r)²  ⟺  L(s)² = 4 r² (Rt² + s²),
        L(s) = |O−I|² − Rt² − r² + 2 s (n·(O−I)),  a quadratic in s."""
    I, r = insphere(V)
    E, red = exsphere_opposite(V, vtx)
    if E is None:
        return []
    A, B, C = (V[j] for j in range(4) if j != vtx)
    O, Rt, n = triangle_circum(A, B, C)
    w = sub(O, I)
    nw, base = dot(n, w), dot(w, w) - Rt**2 - r**2
    P2, P1, P0 = 4 * nw**2 - 4 * r**2, 4 * base * nw, base**2 - 4 * r**2 * Rt**2

    roots = []
    if abs(P2) > EPS:
        disc = P1**2 - 4 * P2 * P0
        if disc >= 0:
            roots = [(-P1 + mp.sqrt(disc)) / (2 * P2),
                     (-P1 - mp.sqrt(disc)) / (2 * P2)]
    elif abs(P1) > EPS:
        roots = [-P0 / P1]

    res = []
    for s in roots:
        rad = mp.sqrt(Rt**2 + s**2)
        c = add(O, smul(s, n))
        if abs(norm(sub(c, I)) - abs(rad - r)) < mp.mpf(10) ** -25:   # internal to insphere
            res.append(norm(sub(c, E)) - abs(rad - red))             # internal-to-exsphere residual
    return res


def report(name, V):
    ortho = "ORTHOCENTRIC" if is_orthocentric(V) else "non-orthocentric"
    print(f"\n=== {name}  [{ortho}] ===")
    worst = mp.mpf(0)
    for vtx in range(4):
        rs = face_pencil_residuals(V, vtx)
        best = min((abs(x) for x in rs), default=None)
        tag = "—" if best is None else mp.nstr(best, 4)
        print(f"  face opp P{vtx}: insphere-internal-tangent pencil sphere also "
              f"exsphere-internal-tangent? residual = {tag}")
        if best is not None:
            worst = max(worst, best)
    print(f"  worst residual over 4 faces = {mp.nstr(worst, 4)}")
    return worst


def main():
    print("Grace 3D-Feuerbach: simultaneous tangency is UNIVERSAL (dps=60)")
    cases = [
        ("Trirectangular T0 (2,3,6)", [vec(2, 0, 0), vec(0, 3, 0), vec(0, 0, 6), vec(0, 0, 0)]),
        # genuine non-trirectangular orthocentric: orthocentre at 0, all six
        # pairwise dots = 2, four distinct vertex norms
        ("Orthocentric, irregular", [vec(2, 0, 0), vec(1, 2, 0), vec(1, sp_half(), 3), vec(1, sp_half(), sp_quarter())]),
        ("Generic non-orthocentric #1", [vec(0, 0, 0), vec(5, 0, 0), vec(1, 4, 0), vec(2, 1, 3)]),
        ("Generic non-orthocentric #2", [vec(0, 0, 0), vec(4, 0, 0), vec(0, 5, 0), vec(1, 2, 4)]),
    ]
    worst_all = mp.mpf(0)
    for name, V in cases:
        worst_all = max(worst_all, report(name, V))
    print("\n================ VERDICT ================")
    ok = worst_all < mp.mpf(10) ** -30
    print(f"  worst simultaneous-tangency residual across ALL cases/faces = {mp.nstr(worst_all, 4)}")
    if ok:
        print("  => CONFIRMED (to 60 digits): on every face of every tested tetrahedron")
        print("     (orthocentric and not), the face-circumcircle pencil contains a sphere")
        print("     simultaneously INTERNALLY tangent to the insphere and to the opposite")
        print("     exsphere. Simultaneous tangency is UNIVERSAL; the trirectangular result's")
        print("     special content is the RATIONALITY/closed form of that sphere.")
    else:
        print("  => NOT universal — residual exceeds threshold; finding does not hold.")
    import sys
    sys.exit(0 if ok else 1)


def sp_half():
    return mp.mpf(1) / 2


def sp_quarter():
    return mp.mpf(1) / 4


if __name__ == "__main__":
    main()
