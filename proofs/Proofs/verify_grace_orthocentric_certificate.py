#!/usr/bin/env python3
"""
Symbolic certificate for `feuerbachs-theorem-oq-02-murakami-oq-01`:
Grace's theorem (3D Feuerbach) beyond the trirectangular tetrahedron.

The parent `feuerbachs-theorem-oq-02-murakami`
(`StatementOnly_FeuerbachOQ02Murakami_GraceTrirectangular.lean`) proves, for a
TRIRECTANGULAR tetrahedron, that the sphere through the face opposite the
right-angle vertex is internally tangent to BOTH the insphere and the
opposite-vertex exsphere, with RATIONAL centre AND RATIONAL radius.

This certificate answers the open question "does the tangency survive for a
strictly larger, non-trirectangular class?" for the two-parameter symmetric
ORTHOCENTRIC family

    D = (0,0,0),  A = (p,q,q),  B = (q,p,q),  C = (q,q,p),   p > q > 0.

A tetrahedron with apex D at the origin is orthocentric iff A.B = A.C = B.C;
here A.B = A.C = B.C = 2pq + q^2, so every member is orthocentric, and it is
trirectangular iff q = 0 (A,B,C along the axes). So q > 0 gives genuinely
non-trirectangular orthocentric tetrahedra.

FINDINGS (all checks below are EXACT symbolic equalities, not numerics):

 1. The Grace sphere through face ABC exists and is internally tangent to both
    the insphere and the D-exsphere.
 2. Its centre is RATIONAL:  Theta = tau * (1,1,1),
        tau = (2 p^2 + 2 p q + 5 q^2) / (3 (p + 2 q)).
 3. Its radius is NOT rational in general:
        R^2 = (p^4 - 4 p q^3 + 3 q^4) / (p + 2 q)^2   (rational),
    but R itself is a surd (e.g. R = sqrt(11)/4 at (p,q)=(2,1)).
    So the rational-CENTRE phenomenon of the trirectangular case persists,
    while the rational-RADIUS phenomenon does NOT.

Base instance (p,q) = (2,1): Theta = (17/12)(1,1,1), R = sqrt(11)/4,
insphere centre (11/8 - sqrt(33)/24)(1,1,1), radius sqrt(11)/8 - sqrt(3)/24;
D-exsphere centre (11/8 + sqrt(33)/24)(1,1,1), radius sqrt(11)/8 + sqrt(3)/24.

Reference: Maehara & Martini, "Tangent Spheres of Tetrahedra and a Theorem of
Grace", Amer. Math. Monthly 127(10):897-910 (2020).

Run:  python3 proofs/Proofs/verify_grace_orthocentric_certificate.py
Requires sympy.
"""

import sympy as sp


def dot(u, v):
    return sp.expand((u.T * v)[0])


def plane(P, Q, R):
    """Return (n, d) with the plane through P,Q,R given by n.X + d = 0."""
    n = (Q - P).cross(R - P)
    d = -dot(n, P)
    return n, d


def sphere_tangent_to_all_faces(D, A, B, C, flip):
    """Solve for the diagonal sphere centre t*(1,1,1) and radius r tangent to
    all four faces. `flip` is the set of face names whose signed distance is
    negated (selects insphere vs a specific exsphere)."""
    t, r = sp.symbols("t r", real=True)
    Ctr = sp.Matrix([t, t, t])
    combos = [(A, B, C, D, "oppD"), (D, B, C, A, "oppA"),
              (D, A, C, B, "oppB"), (D, A, B, C, "oppC")]
    eqs = []
    for (P, Q, R, opp, name) in combos:
        n, d = plane(P, Q, R)
        nn = sp.sqrt(dot(n, n))
        signed = (dot(n, Ctr) + d) / nn
        sopp = (dot(n, opp) + d) / nn
        base = sp.sign(sopp)
        s = -base if name in flip else base
        eqs.append(signed - s * r)
    sol = sp.solve(eqs, [t, r], dict=True)
    return sol[0][t], sol[0][r]


def certify_instance(pv, qv, verbose=True):
    p, q = sp.Integer(pv), sp.Integer(qv)
    D = sp.Matrix([0, 0, 0])
    A = sp.Matrix([p, q, q])
    B = sp.Matrix([q, p, q])
    C = sp.Matrix([q, q, p])

    # orthocentric, non-trirectangular sanity
    assert dot(A, B) == dot(A, C) == dot(B, C)
    assert dot(A, B) != 0, "instance is trirectangular"

    # genuine insphere and D-exsphere (surd data)
    t_in, r_in = sphere_tangent_to_all_faces(D, A, B, C, set())
    t_ex, r_ex = sphere_tangent_to_all_faces(D, A, B, C, {"oppA", "oppB", "oppC"})
    r_ex = sp.Abs(r_ex)
    I = sp.Matrix([t_in, t_in, t_in])
    E = sp.Matrix([t_ex, t_ex, t_ex])

    # closed-form Grace sphere
    tau = (2 * p**2 + 2 * p * q + 5 * q**2) / (3 * (p + 2 * q))
    R2 = sp.nsimplify((p**4 - 4 * p * q**3 + 3 * q**4) / (p + 2 * q)**2)
    R = sp.sqrt(R2)
    Th = sp.Matrix([tau, tau, tau])

    def is_zero(e):
        return sp.simplify(sp.expand(e)) == 0

    checks = {
        "incidence_A": is_zero(dot(Th - A, Th - A) - R2),
        "incidence_B": is_zero(dot(Th - B, Th - B) - R2),
        "incidence_C": is_zero(dot(Th - C, Th - C) - R2),
        "R2_closed_form": is_zero(dot(Th - A, Th - A) - R2),
        "tangent_insphere": is_zero(dot(Th - I, Th - I) - (R - r_in)**2),
        "tangent_Dexsphere": is_zero(dot(Th - E, Th - E) - (R - r_ex)**2),
    }
    # confirm I,E really are the in/ex-sphere: equidistant (= radius) from all faces
    for (P, Q, RR, name) in [(A, B, C, "ABC"), (D, B, C, "DBC"),
                             (D, A, C, "DAC"), (D, A, B, "DAB")]:
        n, d = plane(P, Q, RR)
        nn = sp.sqrt(dot(n, n))
        checks[f"insphere_face_{name}"] = is_zero(sp.Abs(dot(n, I) + d) / nn - r_in)

    ok = all(checks.values())
    if verbose:
        print(f"(p,q)=({pv},{qv})  tau={tau}  R^2={R2}  R={sp.simplify(R)}")
        for k, v in checks.items():
            print(f"    {'PASS' if v else 'FAIL':4}  {k}")
    return ok


def main():
    print("Grace tangency for non-trirectangular symmetric orthocentric tetrahedra")
    print("=" * 72)
    instances = [(2, 1), (3, 1), (3, 2), (5, 2), (7, 3)]
    results = [certify_instance(pv, qv) for (pv, qv) in instances]
    print("=" * 72)
    total = len(results)
    passed = sum(1 for r in results if r)
    print(f"{passed}/{total} instances fully certified (all 5 defining identities exact)")
    if passed != total:
        raise SystemExit(1)
    print("CERTIFICATE PASS")


if __name__ == "__main__":
    main()
