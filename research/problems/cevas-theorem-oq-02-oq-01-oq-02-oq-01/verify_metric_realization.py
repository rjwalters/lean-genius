#!/usr/bin/env python3
"""
Durable build-free verification for the S5 metric-realization lemmas added to
proofs/Proofs/CevasTheoremOQ02OQ01OQ02OQ01.lean (researcher-4, 2026-06-15).

The unification file abstracts the geometric factor g away (proving only the
cancellation (b*g)/(a*g)=b/a with g != 0). The S5 additions connect g to the
GENUINE metric: they prove the kappa-uniform key identities and that the actual
geodesic side-ratio (ratio of sin_kappa of the two geodesic sub-arcs) equals the
weight ratio b/a, derived from the metric quantities sqrt(n^2 - .^2) rather than
the abstract factor.

This script independently re-derives all of it:
  1. ck_metric_BD / ck_metric_DC  (ring identities, exact -> 0)
  2. gSph_sqrt_BD/DC, gHyp_sqrt_BD/DC  (radical closed forms)
  3. spherical_side_ratio_metric  (from genuine S^2 arccos distances)
  4. hyperbolic_side_ratio_metric (from genuine hyperboloid arccosh distances)

Run: python3 verify_metric_realization.py   ->  all checks pass.
"""
import math
import sympy as sp


def check_ring_identities():
    a, b, m = sp.symbols('a b m', real=True)
    nsq = a**2 + 2*a*b*m + b**2
    bd = sp.simplify(nsq - (a + b*m)**2 - b**2*(1 - m**2))
    dc = sp.simplify(nsq - (a*m + b)**2 - a**2*(1 - m**2))
    # hyperbolic sign form used in gHyp_sqrt_BD/DC have-blocks
    bd_h = sp.simplify((a + b*m)**2 - nsq - b**2*(m**2 - 1))
    dc_h = sp.simplify((a*m + b)**2 - nsq - a**2*(m**2 - 1))
    assert bd == 0 and dc == 0 and bd_h == 0 and dc_h == 0, (bd, dc, bd_h, dc_h)
    print("[1] ck_metric_BD/DC ring identities (+ hyperbolic sign forms): exact 0  OK")


def check_radical_forms():
    # sqrt(b^2 * X) = b * sqrt(X) for b >= 0, any X (Real.sqrt_mul + Real.sqrt_sq;
    # for X < 0 both sides are 0). Confirm numerically across signs.
    for b in [0.0, 0.3, 2.0, 7.5]:
        for X in [-3.0, -0.1, 0.0, 0.4, 5.0]:
            lhs = math.sqrt(b**2 * X) if b**2 * X >= 0 else 0.0
            rhs = b * (math.sqrt(X) if X >= 0 else 0.0)
            assert abs(lhs - rhs) < 1e-12, (b, X, lhs, rhs)
    print("[2] sqrt(b^2 * X) = b * sqrt(X) for b>=0 (radical closed form): OK")


def check_spherical_metric_ratio():
    # Genuine S^2: B, C unit vectors with <B,C> = m = cos d(B,C).
    # D' = a*B + b*C, |D'| = n. cos d(B,D') = <B,D'>/n = (a + b m)/n, etc.
    # sin d(B,D) = sqrt(1 - cos^2) = sqrt(n^2 - (a+bm)^2)/n.
    for (m, a, b) in [(0.3, 2.0, 3.0), (-0.4, 1.5, 0.7), (0.8, 5.0, 1.0),
                      (0.05, 1.0, 9.0), (-0.9, 4.0, 2.5)]:
        n = math.sqrt(a**2 + 2*a*b*m + b**2)
        sinBD = math.sqrt(n**2 - (a + b*m)**2) / n
        sinDC = math.sqrt(n**2 - (a*m + b)**2) / n
        # closed forms gSph_sqrt_BD/DC
        assert abs(math.sqrt(n**2 - (a+b*m)**2) - b*math.sqrt(1-m**2)) < 1e-10
        assert abs(math.sqrt(n**2 - (a*m+b)**2) - a*math.sqrt(1-m**2)) < 1e-10
        assert abs(sinBD/sinDC - b/a) < 1e-10, (m, a, b, sinBD/sinDC, b/a)
    print("[3] spherical_side_ratio_metric: sin(BD)/sin(DC) = b/a from S^2 geometry  OK")


def check_hyperbolic_metric_ratio():
    # Hyperboloid: Minkowski form, m = cosh d > 1. sinh d(B,D) = sqrt((a+bm)^2 - n^2)/n.
    for (m, a, b) in [(1.5, 2.0, 3.0), (2.2, 1.0, 0.5), (1.1, 6.0, 1.0),
                      (3.0, 2.0, 2.0), (1.8, 0.5, 4.0)]:
        n = math.sqrt(a**2 + 2*a*b*m + b**2)
        shBD = math.sqrt((a + b*m)**2 - n**2) / n
        shDC = math.sqrt((a*m + b)**2 - n**2) / n
        assert abs(math.sqrt((a+b*m)**2 - n**2) - b*math.sqrt(m**2-1)) < 1e-10
        assert abs(math.sqrt((a*m+b)**2 - n**2) - a*math.sqrt(m**2-1)) < 1e-10
        assert abs(shBD/shDC - b/a) < 1e-10, (m, a, b, shBD/shDC, b/a)
    print("[4] hyperbolic_side_ratio_metric: sinh(BD)/sinh(DC) = b/a from hyperboloid  OK")


if __name__ == "__main__":
    check_ring_identities()
    check_radical_forms()
    check_spherical_metric_ratio()
    check_hyperbolic_metric_ratio()
    print("\nAll metric-realization checks pass.")
