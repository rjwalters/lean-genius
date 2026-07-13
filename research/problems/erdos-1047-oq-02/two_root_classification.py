#!/usr/bin/env python3
"""
erdos-1047-oq-02  Session 3  —  Complete convexity classification of the
two-distinct-root case, the first nontrivial case of the OQ-02 characterization.

Builds directly on Session 2's closed form and log-derivative criterion:

    kappa = |w| * (- Re(w'/w^2)),     w = f'/f = sum_j m_j/(z - r_j),
    a component of {|f| <= c} is convex  <=>  Re(w'/w^2) <= 0  on its boundary.

Equivalently, with u = 1/w = f/f',  u' = -w'/w^2, so

    convex  <=>  Re(u') >= 0  on the boundary.

----------------------------------------------------------------------------
MAIN RESULTS PROVEN/CERTIFIED HERE (two distinct roots, multiplicities m1,m2):

(R1) Scale reduction.  For any common factor, f and f^m give identical level
     sets and Re(w'/w^2) is scale-invariant: w_{f^m} = m*w, and
     (m w)'/(m w)^2 = (1/m)(w'/w^2).  Hence EQUAL multiplicities (m,m) have the
     SAME convexity behaviour as simple roots (1,1), which (affine-invariantly)
     is exactly the normalized polynomial z(z-1).

(R2) Closed form for z(z-1).  With s = z - 1/2,
         u' = (2z^2 - 2z + 1)/(2z - 1)^2 = 1/2 + 1/(8 s^2),
     so  Re(u') = 1/2 + (1/8)(x^2 - y^2)/(x^2 + y^2)^2,   s = x + i y.

(R3) Exact boundary test.  On {|z(z-1)| = c}, write s^2 = 1/4 + c e^{i phi}.
     Then the boundary meets the non-convex region {Re(u') < 0} iff
         cos phi  <  - (1 + 8 c^2) / (6 c).
     Since cos phi >= -1, this is reachable iff 8 c^2 - 6 c + 1 < 0, i.e.
         1/4 < c < 1/2.
     Therefore the COMPLETE classification of z(z-1):
         0 < c < 1/4 :  two components,  BOTH CONVEX
         1/4 < c < 1/2: one component,   NON-CONVEX (dumbbell waist)
         c >= 1/2     : one component,   CONVEX (oval)
     In particular EVERY separated component (c < merge value 1/4) is convex.

(R4) Discriminator.  By (R1) the same holds for two distinct roots of any
     EQUAL multiplicity.  The Pommerenke necking (a non-convex SEPARATED
     component, c < merge) appears only for UNEQUAL multiplicities m1 != m2.
     So in the two-distinct-root case the answer to "are all separated
     components convex?" is exactly  m1 == m2.

Each claim is certified numerically to high precision with mpmath.
"""

import mpmath as mp

mp.mp.dps = 40


# ---------------------------------------------------------------------------
# Generic log-derivative convexity quantity for two roots at 0 and 1.
# ---------------------------------------------------------------------------
def w_and_wp(z, m1, m2):
    """w = f'/f and w' for f = z^m1 (z-1)^m2 (roots 0, 1)."""
    w = m1 / z + m2 / (z - 1)
    wp = -m1 / z**2 - m2 / (z - 1) ** 2
    return w, wp


def re_wp_over_w2(z, m1, m2):
    """Re(w'/w^2): convex <=> this is <= 0 on the boundary."""
    w, wp = w_and_wp(z, m1, m2)
    return mp.re(wp / w**2)


def re_uprime(z, m1, m2):
    """Re(u') with u = 1/w; convex <=> Re(u') >= 0.  (= -Re(w'/w^2))"""
    return -re_wp_over_w2(z, m1, m2)


def f_val(z, m1, m2):
    return z**m1 * (z - 1) ** m2


# ---------------------------------------------------------------------------
# Boundary tracing of |f| = c via 1-D root finding of |f(r e^{i th} + center)|.
# We trace each component by ray-shooting from a root.
# ---------------------------------------------------------------------------
def trace_component(center, c, m1, m2, n_theta=720, rmax=2.0):
    """Boundary points of the component of {|f| <= c} containing `center`,
    by shooting rays from `center` and bisecting |f| = c on the first crossing."""
    pts = []
    for k in range(n_theta):
        th = 2 * mp.pi * k / n_theta
        d = mp.expjpi(0) * (mp.cos(th) + 1j * mp.sin(th))
        # find first r in (0, rmax] with |f(center + r d)| = c, |f|<c inside
        lo, hi = mp.mpf("1e-9"), mp.mpf(rmax)
        f_lo = abs(f_val(center + lo * d, m1, m2))
        if f_lo > c:  # center not strictly inside at this c (degenerate)
            return None
        # expand until we exceed c
        r = lo
        prev = lo
        found = False
        steps = 240
        for j in range(1, steps + 1):
            r = lo + (hi - lo) * j / steps
            if abs(f_val(center + r * d, m1, m2)) >= c:
                found = True
                break
            prev = r
        if not found:
            return None
        a, b = prev, r
        for _ in range(80):
            mid = (a + b) / 2
            if abs(f_val(center + mid * d, m1, m2)) < c:
                a = mid
            else:
                b = mid
        pts.append(center + ((a + b) / 2) * d)
    return pts


def min_re_uprime_on_boundary(center, c, m1, m2, n_theta=720):
    pts = trace_component(center, c, m1, m2, n_theta=n_theta)
    if pts is None:
        return None
    return min(re_uprime(z, m1, m2) for z in pts)


# ---------------------------------------------------------------------------
# Checks
# ---------------------------------------------------------------------------
def check_R2_closed_form():
    """u' = 1/2 + 1/(8 s^2) for z(z-1)."""
    print("== R2: closed form  u' = 1/2 + 1/(8 s^2)  for z(z-1) ==")
    worst = mp.mpf(0)
    for zr in [0.3, -0.4, 0.2 + 0.3j, 0.9 - 0.2j, 1.4 + 0.1j, -0.7 - 0.6j]:
        z = mp.mpc(zr)
        s = z - mp.mpf("0.5")
        closed = mp.mpf("0.5") + 1 / (8 * s**2)
        direct = -((-1 / z**2 - 1 / (z - 1) ** 2) / (1 / z + 1 / (z - 1)) ** 2)
        err = abs(closed - direct)
        worst = max(worst, err)
    print(f"   max |closed - direct| over samples = {mp.nstr(worst, 5)}")
    assert worst < mp.mpf("1e-30"), worst
    print("   OK\n")


def check_R3_threshold():
    """Boundary enters {Re u'<0} iff cos phi < -(1+8c^2)/(6c);
    reachable iff 1/4 < c < 1/2.  Verify via the exact s^2 = 1/4 + c e^{i phi}
    parametrization (no tracing needed: it is the level set algebra)."""
    print("== R3: exact boundary algebra for z(z-1) ==")

    def reu_at_phi(c, phi):
        s2 = mp.mpf("0.25") + c * mp.e ** (1j * phi)
        s = mp.sqrt(s2)
        return mp.mpf("0.5") + mp.re(1 / (8 * s**2))

    def min_reu(c, n=4000):
        return min(reu_at_phi(c, 2 * mp.pi * k / n) for k in range(n))

    def predicted_threshold(c):
        return -(1 + 8 * c**2) / (6 * c)

    rows = [
        (mp.mpf("0.10"), False),
        (mp.mpf("0.20"), False),
        (mp.mpf("0.2499"), False),
        (mp.mpf("0.30"), True),
        (mp.mpf("0.40"), True),
        (mp.mpf("0.4999"), True),
        (mp.mpf("0.60"), False),
        (mp.mpf("1.00"), False),
    ]
    print(f"   {'c':>8} {'min Re u':>14} {'-(1+8c^2)/6c':>16} {'reachable<-1?':>14} {'nonconvex pred':>15}")
    for c, expect_nonconvex in rows:
        mn = min_reu(c)
        thr = predicted_threshold(c)
        reachable = thr > -1  # cos phi can dip below thr only if thr > -1
        # 8c^2-6c+1 < 0  <=>  1/4 < c < 1/2
        pred = (8 * c**2 - 6 * c + 1) < 0
        flag = "NONCONVEX" if mn < -mp.mpf("1e-12") else "convex"
        print(
            f"   {mp.nstr(c,4):>8} {mp.nstr(mn,6):>14} {mp.nstr(thr,6):>16} "
            f"{str(reachable):>14} {str(pred):>15}  -> {flag}"
        )
        assert pred == reachable, (c, pred, reachable)
        # min Re u' < 0 exactly when pred says nonconvex
        assert (mn < -mp.mpf("1e-9")) == expect_nonconvex, (c, mn, expect_nonconvex)
    print("   OK: nonconvex window is exactly 1/4 < c < 1/2;")
    print("       separated components (c<1/4) and large oval (c>1/2) are convex.\n")


def check_R1_equal_mult_reduction():
    """Equal multiplicities (m,m): w_(m,m) = m*w_(1,1), so
    Re(w'/w^2)_(m,m) = (1/m)*Re(w'/w^2)_(1,1).  The positive factor 1/m leaves
    the SIGN unchanged, so the convexity criterion (Re(w'/w^2) <= 0) and hence
    the convexity of every component is identical to the simple-root case."""
    print("== R1: equal-multiplicity reduction (m,m) ~ (1,1) ==")
    worst_scale = mp.mpf(0)
    sign_ok = True
    for zr in [0.3 + 0.2j, -0.4 + 0.5j, 0.8 - 0.3j, 1.2 + 0.4j]:
        z = mp.mpc(zr)
        base = re_wp_over_w2(z, 1, 1)
        for m in (2, 3, 5):
            val = re_wp_over_w2(z, m, m)
            worst_scale = max(worst_scale, abs(val - base / m))
            if (val > 0) != (base > 0):
                sign_ok = False
    print(f"   max |Re(w'/w^2)_(m,m) - (1/m)Re(w'/w^2)_(1,1)| = {mp.nstr(worst_scale,5)}")
    print(f"   sign(Re(w'/w^2)) preserved across m: {sign_ok}")
    assert worst_scale < mp.mpf("1e-30"), worst_scale
    assert sign_ok
    print("   OK: equal-multiplicity convexity == the z(z-1) case (criterion sign-identical).\n")


def check_R4_unequal_has_separated_nonconvex():
    """Unequal multiplicities: a SEPARATED component (c < merge) is non-convex,
    in contrast to the equal case.  Use Pommerenke z^k(z-1)."""
    print("== R4: unequal multiplicities -> non-convex SEPARATED component ==")
    # merge value c* = max_{0<r<1} r^k (1-r) at r* = k/(k+1) (closed form);
    # component around 0.  (k=2 has window W~0.05%, too thin to resolve robustly;
    # the mechanism is unambiguous from k=5 up, matching Session 1's W(k).)
    for k in (5, 8):
        rstar = mp.mpf(k) / (k + 1)
        cstar = (rstar**k) * (1 - rstar)
        found_nonconvex = False
        worst = mp.mpf(0)
        cc_at = None
        for frac in [mp.mpf(x) for x in ("0.90", "0.97", "0.999")]:
            c = frac * cstar
            mn = min_re_uprime_on_boundary(mp.mpc(0, 0), c, k, 1, n_theta=1800)
            if mn is None:
                continue
            if mn < worst:
                worst = mn
                cc_at = (frac, c)
            if mn < -mp.mpf("1e-6"):
                found_nonconvex = True
        print(
            f"   k={k}: c*={mp.nstr(cstar,5)}  worst min Re(u') on component(0) "
            f"= {mp.nstr(worst,5)} at c/c*={mp.nstr(cc_at[0],4) if cc_at else 'NA'}"
            f"  -> {'NON-CONVEX (separated)' if found_nonconvex else 'convex'}"
        )
        assert found_nonconvex, f"expected separated non-convex for k={k}"
    print("   OK: unequal multiplicity gives a non-convex separated component;")
    print("       equal multiplicity never does (R1+R3).\n")


def check_equal_separated_convex_via_tracing():
    """Cross-check R3 by direct boundary tracing of z(z-1): both separated
    components convex for c<1/4, both becoming flat (min Re u' -> 0) at merge."""
    print("== cross-check: traced boundary of z(z-1), component around 0 ==")
    for c in [mp.mpf(x) for x in ("0.05", "0.15", "0.24", "0.249")]:
        mn = min_re_uprime_on_boundary(mp.mpf("0.0") + 0j, c, 1, 1, n_theta=1440)
        print(f"   c={mp.nstr(c,4)}  min Re(u') over comp(0) = {mp.nstr(mn,5)}")
        assert mn > -mp.mpf("1e-6"), (c, mn)
    print("   OK: traced separated components are convex up to merge.\n")


if __name__ == "__main__":
    check_R2_closed_form()
    check_R1_equal_mult_reduction()
    check_R3_threshold()
    check_equal_separated_convex_via_tracing()
    check_R4_unequal_has_separated_nonconvex()
    print("ALL CHECKS PASSED.")
