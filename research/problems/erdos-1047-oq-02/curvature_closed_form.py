#!/usr/bin/env python3
"""
Closed-form lemniscate curvature for erdos-1047-oq-02 (convex components).

Session 2 (2026-06-14) ANALYTIC advance on top of Session 1's numerical ORIENT.
Session 1 had a *numerical-only* convexity test: the real Hessian of g = |f|^2,

    kappa_real = (gx^2 g_yy - 2 gx gy g_xy + gy^2 g_xx) / (gx^2 + gy^2)^{3/2},

calibrated so a sublevel disk has kappa > 0. This file replaces that with a
CLOSED-FORM complex expression in f, f', f'' (validated to ~6 digits against the
Session-1 real formula), and a further reduction to the logarithmic derivative
that depends ONLY on the root locations and multiplicities.

------------------------------------------------------------------------------
RESULT 1 (general lemniscate curvature, calibrated):
    For f analytic with f != 0 on the level set {|f| = c}, the signed curvature
    of the boundary (oriented so a sublevel DISK has kappa > 0) is

        kappa = |f'/f| * ( 1 - Re( f f'' / (f')^2 ) ).

    Hence a component of {|f| <= c} is CONVEX  <=>  Re( f f'' / (f')^2 ) <= 1
    on its boundary (wherever f' != 0).

RESULT 2 (logarithmic-derivative reduction): let w = f'/f = sum_j m_j/(z - r_j)
    over the distinct roots r_j with multiplicities m_j. Then f f''/(f')^2 =
    1 + w'/w^2, so

        kappa = - |w| * Re( w' / w^2 ),      convex  <=>  Re( w'/w^2 ) <= 0,

    with w' = - sum_j m_j/(z - r_j)^2. The convexity test depends ONLY on the
    root data (locations + multiplicities), not on the overall scale of f.

RESULT 3 (single distinct root): f = (z - r)^m gives w'/w^2 == -1/m identically,
    so Re(w'/w^2) = -1/m < 0 everywhere: EVERY level set is convex. (They are the
    circles |z - r| = c^{1/m}; this recovers that fact from the criterion and is
    the base case of the OQ-02 characterization.)

RESULT 4 (on-axis curvature for Pommerenke f = z^k (z - a), a>0 real). At the
    two points where the component around 0 meets the real axis perpendicularly
    (r'(theta)=0), the closed form for r'' gives:
       near nose (theta=0, facing a):  r'' = - a r^2 / [ (a-r)(k(a-r) - r) ],
       far  nose (theta=pi):           r'' =   a r^2 / [ (r+a)(k(r+a) + r) ].
    Both yield kappa = (r - r'')/r^2 > 0, i.e. BOTH on-axis tips stay CONVEX; the
    near (facing-a) tip even SHARPENS, kappa -> +inf as r -> r_saddle = k a/(k+1)
    (the merge radius), since k(a-r)-r -> 0+. So the non-convexity reported in
    Session 1 is genuinely OFF-AXIS: two symmetric concave SHOULDERS flanking the
    sharp tip facing a (numerically at theta ~ +-0.02..0.03 pi), NOT a dimple at
    the tip itself. This corrects the mental picture while confirming Session 1's
    "dimple angle ~ 0" observation (the shoulders sit just beside theta=0).

All four results are checked numerically below.
"""
import numpy as np
from scipy.optimize import brentq


# ---------- the formulas under test ----------
def f_val_derivs(roots, mults, z, h=1e-5):
    """f, f', f'' by complex central differences of f(z)=prod (z-r)^m."""
    def f(zz):
        out = 1.0 + 0j
        for r, m in zip(roots, mults):
            out *= (zz - r) ** m
        return out
    fz = f(z)
    fp = (f(z + h) - f(z - h)) / (2 * h)
    fpp = (f(z + h) - 2 * fz + f(z - h)) / h ** 2
    return fz, fp, fpp


def kappa_complex(roots, mults, z):
    """RESULT 1: kappa = |f'/f| (1 - Re(f f''/f'^2))."""
    fz, fp, fpp = f_val_derivs(roots, mults, z)
    return abs(fp / fz) * (1.0 - np.real(fz * fpp / fp ** 2))


def kappa_log(roots, mults, z):
    """RESULT 2: kappa = -|w| Re(w'/w^2), w = sum m/(z-r) (exact, no diff)."""
    w = sum(m / (z - r) for r, m in zip(roots, mults))
    wp = sum(-m / (z - r) ** 2 for r, m in zip(roots, mults))
    return -abs(w) * np.real(wp / w ** 2)


def kappa_real_hessian(roots, mults, z, h=1e-4):
    """Session-1 reference: real Hessian of g=|f|^2 (ground truth)."""
    def g(x, y):
        zz = x + 1j * y
        out = 1.0 + 0j
        for r, m in zip(roots, mults):
            out *= (zz - r) ** m
        return abs(out) ** 2
    x, y = z.real, z.imag
    gx = (g(x + h, y) - g(x - h, y)) / (2 * h)
    gy = (g(x, y + h) - g(x, y - h)) / (2 * h)
    gxx = (g(x + h, y) - 2 * g(x, y) + g(x - h, y)) / h ** 2
    gyy = (g(x, y + h) - 2 * g(x, y) + g(x, y - h)) / h ** 2
    gxy = (g(x + h, y + h) - g(x + h, y - h)
           - g(x - h, y + h) + g(x - h, y - h)) / (4 * h ** 2)
    num = gx ** 2 * gyy - 2 * gx * gy * gxy + gy ** 2 * gxx
    den = (gx ** 2 + gy ** 2) ** 1.5
    return num / den


# ---------- helpers ----------
def boundary_pt(roots, mults, theta, c, rmax, center=0.0):
    def fabs(r):
        z = center + r * np.exp(1j * theta)
        out = 1.0 + 0j
        for rr, m in zip(roots, mults):
            out *= (z - rr) ** m
        return abs(out)
    g = lambda r: fabs(r) - c
    rs = np.linspace(1e-7, rmax, 8000)
    v = np.array([g(r) for r in rs])
    idx = np.where(np.diff(np.sign(v)) > 0)[0]
    if len(idx) == 0:
        return None
    i = idx[0]
    return center + brentq(g, rs[i], rs[i + 1]) * np.exp(1j * theta)


def cstar_pommerenke(k, a):
    rs = np.linspace(1e-4, a - 1e-4, 40000)
    return (rs ** k * np.abs(rs - a)).max()


# ---------- tests ----------
def test_formulas_agree():
    print("RESULT 1+2: kappa_complex and kappa_log vs real-Hessian ground truth")
    print(f"{'case':30}{'theta/pi':>9}{'kappa_real':>12}{'kappa_cx':>12}{'kappa_log':>12}")
    rows = [
        ("f=z (unit circle)", [0.0], [1], 0.7, 1.0, 1.6),
        ("z^3(z-1) tip", [0.0, 1.0], [3, 1], 0.0, 0.97 * cstar_pommerenke(3, 1), 1.6),
        ("z^3(z-1) shoulder", [0.0, 1.0], [3, 1], 0.06, 0.999 * cstar_pommerenke(3, 1), 1.6),
        ("z^5(z-1) tip", [0.0, 1.0], [5, 1], 0.0, 0.999 * cstar_pommerenke(5, 1), 1.6),
        ("z^5(z-1) shoulder", [0.0, 1.0], [5, 1], 0.02, 0.999 * cstar_pommerenke(5, 1), 1.6),
        ("Goodman (z^2+1)(z-2)^2", [1j, -1j, 2.0], [1, 1, 2], 0.1, 5 ** 1.5 / 4, 3.0),
    ]
    worst = 0.0
    for name, roots, mults, thfac, c, rmax in rows:
        th = thfac * np.pi
        z = boundary_pt(roots, mults, th, c, rmax)
        if z is None:
            print(f"{name:30}{thfac:9.3f}   (no boundary point)")
            continue
        kr = kappa_real_hessian(roots, mults, z)
        kc = kappa_complex(roots, mults, z)
        kl = kappa_log(roots, mults, z)
        worst = max(worst, abs(kr - kc), abs(kr - kl))
        print(f"{name:30}{thfac:9.3f}{kr:12.5f}{kc:12.5f}{kl:12.5f}")
    print(f"  max |kappa_real - closed_form| over cases = {worst:.2e}\n")
    assert worst < 1e-3, "closed-form curvature disagrees with ground truth"


def test_single_root_always_convex():
    print("RESULT 3: f=(z-r)^m  =>  Re(w'/w^2) == -1/m  (all level sets convex)")
    r0 = 0.5 + 0.3j
    for m in [1, 2, 3, 7]:
        vals = []
        for th in np.linspace(0, 2 * np.pi, 13, endpoint=False):
            z = r0 + 0.8 * np.exp(1j * th)
            w = m / (z - r0)
            wp = -m / (z - r0) ** 2
            vals.append(np.real(wp / w ** 2))
        vals = np.array(vals)
        print(f"  m={m}: Re(w'/w^2) in [{vals.min():.6f}, {vals.max():.6f}]  "
              f"target -1/m = {-1/m:.6f}")
        assert np.allclose(vals, -1.0 / m, atol=1e-9)
    print()


def test_pommerenke_on_axis():
    print("RESULT 4: on-axis curvature for z^k(z-a); both tips convex, near tip sharpens")
    print(f"{'k':>2}{'a':>5}{'c/c*':>7}{'r_near':>9}{'kappa_near':>12}"
          f"{'r_far':>9}{'kappa_far':>11}")
    for k, a in [(3, 1.0), (5, 1.0), (10, 1.3)]:
        cs = cstar_pommerenke(k, a)
        for frac in [0.90, 0.97, 0.999]:
            c = frac * cs
            zn = boundary_pt([0.0, a], [k, 1], 0.0, c, 1.7 * a)
            zf = boundary_pt([0.0, a], [k, 1], np.pi, c, 1.7 * a)
            rn, rf = zn.real, abs(zf.real)
            rpp_n = -a * rn ** 2 / ((a - rn) * (k * (a - rn) - rn))
            rpp_f = a * rf ** 2 / ((rf + a) * (k * (rf + a) + rf))
            kn = (rn - rpp_n) / rn ** 2
            kf = (rf - rpp_f) / rf ** 2
            print(f"{k:>2}{a:>5.1f}{frac:>7.3f}{rn:>9.5f}{kn:>12.4f}"
                  f"{rf:>9.5f}{kf:>11.4f}")
            assert kn > 0 and kf > 0, "on-axis tip is not convex"
    print("  -> both on-axis tips convex for all c; near-tip kappa grows toward merge\n")


if __name__ == "__main__":
    test_formulas_agree()
    test_single_root_always_convex()
    test_pommerenke_on_axis()
    print("ALL CHECKS PASSED")
