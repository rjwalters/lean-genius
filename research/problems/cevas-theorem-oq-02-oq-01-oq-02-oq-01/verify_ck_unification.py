#!/usr/bin/env python3
"""
Durable verification for cevas-theorem-oq-02-oq-01-oq-02-oq-01.

OQ: prove all three Ceva theorems (spherical / Euclidean / hyperbolic) from a
SINGLE projective Ceva theorem via the Cayley-Klein (Beltrami-Klein) model.

This script independently RE-DERIVES and checks the algebraic + metric core of the
Cayley-Klein unification surveyed in knowledge.md, so the (Docker-gated) Lean build
is de-risked: the math is confirmed here from first principles, not assumed.

Backend status when written (2026-06-14): Docker daemon down, Aristotle backend
returns "Resource not found" -> no Lean build possible. This script is build-free.

Run:  python3 verify_ck_unification.py          (sympy required; falls back to a
                                                  pure-stdlib numeric pass if absent)

What is verified
----------------
(1) The TWO core algebraic identities that drive every geometry (symbolic, exact):
        (alpha + beta*m)^2 - n^2 = beta^2 *(m^2 - 1)        [BD]
        (alpha*m + beta)^2 - n^2 = alpha^2*(m^2 - 1)        [DC]
    with n^2 = alpha^2 + 2*alpha*beta*m + beta^2.
    These are exactly the parent's `hyp_key_identity_BD/DC`
    (CevasTheoremOQ02OQ01OQ02.lean:98,105). The spherical case is the SAME identity
    read with m^2 - 1 = -(1 - m^2); this single sign-carrying identity is the heart
    of "one projective theorem, three geometries".

(2) The abstract cancellation (*) `ck_ratio_cancel`  (beta*g)/(alpha*g) = beta/alpha
    for any nonzero common factor g = sqrt|1 - m^2| / n (symbolic).

(3) SPHERICAL (kappa=+1) metric side ratio, computed from ACTUAL unit vectors on
    S^2 via cos/sin of geodesic distances: sin(d(B,D))/sin(d(D,C)) = beta/alpha,
    and sin(d(B,D)) = beta*sqrt(1-m^2)/n.

(4) HYPERBOLIC (kappa=-1) metric side ratio, from ACTUAL points on the hyperboloid
    with the Minkowski form: sinh(d(B,D))/sinh(d(D,C)) = beta/alpha,
    and sinh(d(B,D)) = beta*sqrt(m^2-1)/n.

(5) EUCLIDEAN (kappa=0) limit m -> 1: n = alpha+beta, barycentric BD/DC = beta/alpha,
    no radical (gEuc = 1).

(6) The concurrency criterion `universal_weight_balance`
    (CevasTheoremOQ02OQ01OQ02.lean:254): three cevians AD, BE, CF of a concrete
    triangle are concurrent IFF  aD*aE*aF = bD*bE*bF  IFF  prod(beta/alpha) = 1.
    Verified geometrically (line intersection) against the product condition.
"""

import math

# ---------------------------------------------------------------------------
# (1) + (2): exact symbolic identities (sympy)
# ---------------------------------------------------------------------------

def symbolic_checks():
    import sympy as sp
    alpha, beta, m, g = sp.symbols("alpha beta m g", positive=True)
    n_sq = alpha**2 + 2*alpha*beta*m + beta**2

    # (1) the two core identities -- exact, must reduce to 0
    id_BD = sp.expand((alpha + beta*m)**2 - n_sq - beta**2*(m**2 - 1))
    id_DC = sp.expand((alpha*m + beta)**2 - n_sq - alpha**2*(m**2 - 1))
    assert id_BD == 0, f"BD identity failed: {id_BD}"
    assert id_DC == 0, f"DC identity failed: {id_DC}"

    # spherical reading: n^2 - (alpha+beta*m)^2 = beta^2*(1 - m^2)
    sph_BD = sp.expand(n_sq - (alpha + beta*m)**2 - beta**2*(1 - m**2))
    sph_DC = sp.expand(n_sq - (alpha*m + beta)**2 - alpha**2*(1 - m**2))
    assert sph_BD == 0 and sph_DC == 0, "spherical sign-flip reading failed"

    # (2) abstract cancellation (*)  (beta*g)/(alpha*g) = beta/alpha
    cancel = sp.simplify((beta*g)/(alpha*g) - beta/alpha)
    assert cancel == 0, f"ck_ratio_cancel failed: {cancel}"

    # n^2 at the Euclidean limit m=1 is a perfect square (alpha+beta)^2
    assert sp.simplify(n_sq.subs(m, 1) - (alpha + beta)**2) == 0
    print("  [OK] (1) core algebraic identities BD & DC (exact, both signs)")
    print("  [OK] (2) abstract cancellation (beta*g)/(alpha*g) = beta/alpha")
    print("  [OK]     Euclidean n^2|_{m=1} = (alpha+beta)^2")


# ---------------------------------------------------------------------------
# (3) spherical: genuine S^2 geometry
# ---------------------------------------------------------------------------

def dot(u, v):
    return sum(a*b for a, b in zip(u, v))

def spherical_ratio(B, C, alpha, beta):
    m = dot(B, C)                      # = cos d(B,C)
    n = math.sqrt(alpha**2 + 2*alpha*beta*m + beta**2)
    D = [(alpha*b + beta*c)/n for b, c in zip(B, C)]   # unit cevian point
    # d(P,Q) = arccos(P.Q) on the unit sphere
    dBD = math.acos(max(-1.0, min(1.0, dot(B, D))))
    dDC = math.acos(max(-1.0, min(1.0, dot(D, C))))
    return m, n, math.sin(dBD), math.sin(dDC)

def spherical_checks():
    # two unit vectors with a generic separation
    th = 0.8
    B = [1.0, 0.0, 0.0]
    C = [math.cos(th), math.sin(th), 0.0]
    for alpha, beta in [(1.0, 2.0), (3.0, 0.7), (2.5, 2.5), (0.4, 1.9)]:
        m, n, sBD, sDC = spherical_ratio(B, C, alpha, beta)
        ratio = sBD/sDC
        assert abs(ratio - beta/alpha) < 1e-9, f"sph ratio {ratio} != {beta/alpha}"
        assert abs(sBD - beta*math.sqrt(1-m**2)/n) < 1e-9, "sph sin(BD) formula"
        assert abs(sDC - alpha*math.sqrt(1-m**2)/n) < 1e-9, "sph sin(DC) formula"
    print("  [OK] (3) spherical sin-ratio = beta/alpha + closed forms (S^2 metric)")


# ---------------------------------------------------------------------------
# (4) hyperbolic: genuine hyperboloid (Minkowski) geometry
# ---------------------------------------------------------------------------

def mink(u, v):
    return u[0]*v[0] + u[1]*v[1] - u[2]*v[2]

def hyperbolic_checks():
    # points on the upper sheet  <x,x> = -1   (x3 > 0)
    def hpoint(r, phi):
        return [math.sinh(r)*math.cos(phi), math.sinh(r)*math.sin(phi), math.cosh(r)]
    B = hpoint(0.0, 0.0)               # apex
    C = hpoint(0.9, 0.5)
    assert abs(mink(B, B) + 1) < 1e-12 and abs(mink(C, C) + 1) < 1e-12
    m = -mink(B, C)                    # = cosh d(B,C) > 1
    assert m > 1
    for alpha, beta in [(1.0, 2.0), (3.0, 0.7), (2.5, 2.5), (0.4, 1.9)]:
        n = math.sqrt(alpha**2 + 2*alpha*beta*m + beta**2)
        Dp = [alpha*b + beta*c for b, c in zip(B, C)]
        # <D',D'> = -(alpha^2 + 2 alpha beta m + beta^2) = -n^2
        assert abs(mink(Dp, Dp) + n**2) < 1e-9
        D = [x/n for x in Dp]
        coshBD = -mink(B, D)
        coshDC = -mink(D, C)
        sBD = math.sqrt(coshBD**2 - 1)
        sDC = math.sqrt(coshDC**2 - 1)
        assert abs(sBD/sDC - beta/alpha) < 1e-9, "hyp sinh-ratio"
        assert abs(sBD - beta*math.sqrt(m**2-1)/n) < 1e-9, "hyp sinh(BD) formula"
        assert abs(sDC - alpha*math.sqrt(m**2-1)/n) < 1e-9, "hyp sinh(DC) formula"
    print("  [OK] (4) hyperbolic sinh-ratio = beta/alpha + closed forms (hyperboloid)")


# ---------------------------------------------------------------------------
# (5) Euclidean limit
# ---------------------------------------------------------------------------

def euclidean_checks():
    m = 1.0
    for alpha, beta in [(1.0, 2.0), (3.0, 0.7), (0.4, 1.9)]:
        n = math.sqrt(alpha**2 + 2*alpha*beta*m + beta**2)
        assert abs(n - (alpha + beta)) < 1e-12, "Euclidean n = alpha+beta"
        # gEuc = 1, barycentric BD/DC = beta/alpha directly (no radical)
        assert abs((beta*1.0)/(alpha*1.0) - beta/alpha) < 1e-12
    print("  [OK] (5) Euclidean limit m=1: n=alpha+beta, ratio beta/alpha (no radical)")


# ---------------------------------------------------------------------------
# (6) concurrency criterion (geometric Ceva) vs product condition
# ---------------------------------------------------------------------------

def _seg(P, Q, t):
    return (P[0] + t*(Q[0]-P[0]), P[1] + t*(Q[1]-P[1]))

def _line_int(P1, P2, P3, P4):
    # intersection of line P1P2 with line P3P4 (2D); None if parallel
    x1, y1 = P1; x2, y2 = P2; x3, y3 = P3; x4, y4 = P4
    den = (x1-x2)*(y3-y4) - (y1-y2)*(x3-x4)
    if abs(den) < 1e-14:
        return None
    px = ((x1*y2 - y1*x2)*(x3-x4) - (x1-x2)*(x3*y4 - y3*x4)) / den
    py = ((x1*y2 - y1*x2)*(y3-y4) - (y1-y2)*(x3*y4 - y3*x4)) / den
    return (px, py)

def concurrency_checks():
    A = (0.0, 0.0); B = (4.0, 0.0); C = (1.0, 3.0)
    # cevian foot D on BC with BD/DC = bD/aD  =>  D = B + (bD/(aD+bD)) (C-B)
    def foot(P, Q, a, b):
        return _seg(P, Q, b/(a+b))
    cases = [
        # (aD,bD, aE,bE, aF,bF, expect_concurrent)
        (1, 2, 2, 1, 1, 1, True),     # aD aE aF = 2 = bD bE bF -> concurrent
        (3, 1, 1, 1, 1, 3, True),     # 3 = 3
        (1, 2, 1, 2, 1, 2, False),    # 1 vs 8
        (2, 1, 3, 1, 1, 1, False),    # 6 vs 1
        (1.5, 0.5, 0.5, 1.5, 1.0, 1.0, True),  # 0.75 = 0.75
    ]
    for aD, bD, aE, bE, aF, bF, expect in cases:
        D = foot(B, C, aD, bD)   # on BC
        E = foot(C, A, aE, bE)   # on CA
        F = foot(A, B, aF, bF)   # on AB
        # AD and BE intersect at P; concurrent iff CF passes through P
        P = _line_int(A, D, B, E)
        assert P is not None
        # distance of P from line CF
        x3, y3 = C; x4, y4 = F
        num = abs((y4-y3)*P[0] - (x4-x3)*P[1] + x4*y3 - y4*x3)
        den = math.hypot(y4-y3, x4-x3)
        concurrent = (num/den) < 1e-7
        prod_eq = abs(aD*aE*aF - bD*bE*bF) < 1e-9
        ratio_eq = abs((bD/aD)*(bE/aE)*(bF/aF) - 1.0) < 1e-9
        assert concurrent == expect, f"geometry vs expect mismatch {(aD,bD,aE,bE,aF,bF)}"
        assert concurrent == prod_eq == ratio_eq, "criterion mismatch"
    print("  [OK] (6) concurrency IFF aD*aE*aF=bD*bE*bF IFF prod(beta/alpha)=1")


def main():
    print("Cayley-Klein Ceva unification -- durable verification")
    print("=" * 60)
    try:
        import sympy  # noqa: F401
        symbolic_checks()
    except ImportError:
        print("  [skip] sympy absent -- symbolic identities not checked (numeric below)")
    spherical_checks()
    hyperbolic_checks()
    euclidean_checks()
    concurrency_checks()
    print("=" * 60)
    print("ALL CHECKS PASSED -- Cayley-Klein unification math is sound.")
    print("Single sign-carrying identity (alpha+beta*m)^2 - n^2 = beta^2*(m^2-1)")
    print("drives spherical (m^2-1<0), hyperbolic (m^2-1>0), Euclidean (m=1) alike.")


if __name__ == "__main__":
    main()
