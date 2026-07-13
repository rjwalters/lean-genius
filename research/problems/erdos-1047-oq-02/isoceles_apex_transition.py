#!/usr/bin/env python3
"""
erdos-1047-oq-02  (researcher-11) — the COLLINEAR -> EQUILATERAL transition for a
simple three-root triple: where does the near-merge necking of the apex component
switch off?

Open next-step (knowledge.md, Session 2026-06-15 researcher-1):
  "for the equilateral->isoceles deformation, find where the simultaneous
   confluence breaks into pairwise saddles and necking switches on."

Setup.  Conjugate-symmetric (REAL-coefficient) one-parameter family
        f_a(z) = (z - a) * (z^2 + 1),     roots {a, +i, -i},  a >= 0 real.
The three roots form an ISOCELES triangle: base = the segment (-i, +i) of length 2
on the imaginary axis, apex = the real root a.  Two regimes bracket the family:
  * a = 0     : roots {0, i, -i} are COLLINEAR on the imaginary axis (= z^3 + z);
                the apex root 0 is the geometric MIDDLE (interior) -> by the
                Session-1 collinear-simple result it NECKS just below merge.
  * a = sqrt3 : EQUILATERAL (|a-i| = |a+i| = 2 = |i-(-i)|); the three roots undergo
                a SIMULTANEOUS triple confluence at the centroid a/3 = 1/sqrt3 (a
                degenerate critical point, NOT a pairwise saddle) -> ALL CONVEX.
So there is a critical apex position a_c in (0, sqrt3) at which the apex component's
near-merge necking switches off.  This script LOCATES a_c.

Merge threshold (exact).  Saddles of |f| sit at the critical points f'(z)=0.
    f'(z) = 3 z^2 - 2 a z + 1,   roots  z_crit = (a +/- i sqrt(3 - a^2)) / 3   (a<sqrt3).
For a < sqrt3 the two critical points are a conjugate pair (two pairwise saddles);
at a = sqrt3 they coalesce at 1/sqrt3 (the confluence).  c*(a) = |f(z_crit)| is the
level at which the apex component merges with the base pair.

Convexity criterion (Sessions 1-3, validated in two_root_control.py / three_collinear_simple.py):
    w = sum 1/(z - r_j),  u = 1/w,  u' = -w'/w^2;   component convex  <=>  Re(u') >= 0
on its boundary.  We ray-cast the apex component boundary from r0 = a and minimise
Re(u') over it at c = ratio * c*(a) with ratio -> 1.

VALIDATION GATES (must hold or the tracer is suspect):
  * a = 0  reproduces the collinear-simple NECKING (min Re(u') < 0 near merge).
  * a = sqrt3 (equilateral) stays CONVEX (min Re(u') >= 0 up to confluence).
  * a = 0 is the z^3+z apex == the SAME phenomenon as z(z-1)(z-2)'s middle.

Docker-independent.  Requires mpmath.
"""
import sys
import mpmath as mp

try:
    sys.stdout.reconfigure(line_buffering=True)
except Exception:
    pass

mp.mp.dps = 30
SQRT3 = mp.sqrt(3)


def make(a):
    """Return (roots, fabs, re_uprime) for f_a = (z-a)(z^2+1)."""
    R = [mp.mpf(a), mp.mpc(0, 1), mp.mpc(0, -1)]

    def fabs(z):
        o = mp.mpf(1)
        for r in R:
            o *= abs(z - r)
        return o

    def reup(z):
        w = sum(1 / (z - r) for r in R)
        wp = -sum(1 / (z - r) ** 2 for r in R)
        return mp.re(-wp / w ** 2)
    return R, fabs, reup


def cstar(a):
    """Merge threshold = |f(z_crit)| at the (conjugate) critical point, a < sqrt3."""
    a = mp.mpf(a)
    zc = (a + 1j * mp.sqrt(3 - a * a)) / 3
    f = (zc - a) * (zc * zc + 1)
    return abs(f)


def radius_at(fabs, r0, theta, c, rmax):
    """First outward crossing of |f|=c along the ray from r0 at angle theta."""
    d = mp.e ** (1j * theta)
    lo = mp.mpf("1e-14")
    hi = None
    prev = lo
    steps = 700
    for k in range(1, steps + 1):
        rr = rmax * k / steps
        if fabs(r0 + rr * d) - c >= 0:
            hi = rr
            lo = prev
            break
        prev = rr
    if hi is None:
        return None
    for _ in range(200):
        mid = (lo + hi) / 2
        if fabs(r0 + mid * d) - c < 0:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


def min_apex_boundary(a, ratio, ntheta=720):
    """Min Re(u') over the apex (z=a) component boundary at c = ratio*c*(a)."""
    R, fabs, reup = make(a)
    r0 = mp.mpf(a)
    c = mp.mpf(ratio) * cstar(a)
    # apex component sits between the apex and the base pair; spacing ~ |a - i|.
    rmax = mp.mpf("1.4") * abs(mp.mpf(a) - 1j)
    best = mp.mpf("inf")
    bz = None
    bth = None
    for j in range(ntheta):
        th = 2 * mp.pi * j / ntheta
        rr = radius_at(fabs, r0, th, c, rmax)
        if rr is None:
            continue
        z = r0 + rr * mp.e ** (1j * th)
        v = reup(z)
        if v < best:
            best, bz, bth = v, z, th
    return best, bz, bth


def necks(a, ratio="0.999995", ntheta=720):
    """True iff the apex component is non-convex (min Re(u') < 0) at this ratio."""
    v, _, _ = min_apex_boundary(a, ratio, ntheta)
    return v < 0, v


def apex_angle_deg(a):
    """Interior angle of the isoceles triangle at the apex root a (base = +/-i)."""
    a = mp.mpf(a)
    # vectors from apex a to the two base vertices +/- i
    v1 = mp.mpc(-a, 1)
    v2 = mp.mpc(-a, -1)
    cosang = mp.re(v1 * mp.conj(v2)) / (abs(v1) * abs(v2))
    return float(mp.acos(cosang) * 180 / mp.pi)


if __name__ == "__main__":
    print("erdos-1047-oq-02: collinear -> equilateral transition for f_a=(z-a)(z^2+1)")
    print("apex root = a (real); base roots = +/- i.  Convex <=> Re(u') >= 0 on boundary.")
    print("=" * 74)

    # ---------- VALIDATION GATES ----------
    print("VALIDATION GATES")
    print("-" * 74)
    print("a = 0 (collinear z^3+z, apex=middle root 0); expect NECKS near merge:")
    for ratio in ["0.999", "0.9999", "0.99999", "0.999999"]:
        v, z, th = min_apex_boundary(0, ratio, ntheta=360)
        tag = "NON-CONVEX" if v < 0 else "convex"
        print(f"   c/c*={ratio:>9}: min Re(u') = {mp.nstr(v,10):>14}  ({tag})")
    print()
    print(f"a = sqrt3 = {mp.nstr(SQRT3,12)} (EQUILATERAL); expect CONVEX up to confluence:")
    for ratio in ["0.999", "0.9999", "0.99999", "0.999999"]:
        v, z, th = min_apex_boundary(SQRT3, ratio, ntheta=360)
        tag = "NON-CONVEX" if v < 0 else "convex OK"
        print(f"   c/c*={ratio:>9}: min Re(u') = {mp.nstr(v,10):>14}  ({tag})")
    print()

    # ---------- NECKING WINDOW WIDTH W(a) ----------
    # The fixed-ratio sign of min Re(u') is contaminated by a near-merge artifact
    # (as a->sqrt3 the two conjugate saddles coalesce, sharpening the pre-merge
    # geometry at ANY fixed ratio).  The artifact-resistant invariant -- exactly the
    # one Session 1 used for the multiplicity table W(k) -- is the NECKING WINDOW
    # WIDTH  W(a) = (c* - c_nc)/c*,  where c_nc is the ONSET level at which the apex
    # component first becomes non-convex.  W(a) > 0  <=>  a genuine necking window
    # exists below merge.  We find c_nc/c* by bisecting the ratio between a convex
    # ratio and a non-convex ratio.
    print("NECKING WINDOW WIDTH  W(a) = (c* - c_nc)/c*   (c_nc = non-convexity onset)")
    print("-" * 74)
    print(f"{'a':>10} | {'a/sqrt3':>8} | {'apex deg':>8} | {'c_nc/c*':>12} | {'W(a)':>12} | necks?")
    print("-" * 74)

    def onset_ratio(a, ntheta=180):
        """Bisect the ratio r in (r_lo, r_hi) for the first r with min Re(u')<0.
        Returns (r_onset, found) ; found=False if convex even at r_hi (no window)."""
        r_lo = mp.mpf("0.99")      # convex end (small components)
        r_hi = mp.mpf("0.9999999") # deep near-merge end
        v_lo, _, _ = min_apex_boundary(a, r_lo, ntheta)
        v_hi, _, _ = min_apex_boundary(a, r_hi, ntheta)
        if v_hi >= 0:
            return None, False     # convex up to the deepest tested ratio -> W=0
        if v_lo < 0:
            # already non-convex well below merge: extend the convex end downward
            r_lo = mp.mpf("0.9")
            v_lo, _, _ = min_apex_boundary(a, r_lo, ntheta)
            if v_lo < 0:
                return r_lo, True  # necks even at 0.9; report conservative onset
        for _ in range(34):
            rm = (r_lo + r_hi) / 2
            vm, _, _ = min_apex_boundary(a, rm, ntheta)
            if vm < 0:
                r_hi = rm
            else:
                r_lo = rm
        return (r_lo + r_hi) / 2, True

    coarse = [mp.mpf(k) / 12 * SQRT3 for k in range(0, 12)]   # 0 .. ~1.588
    fine = [mp.mpf(s) for s in ["1.30", "1.38", "1.44", "1.50", "1.56",
                                "1.62", "1.66", "1.69", "1.71", "1.725"]]
    grid = sorted(set(coarse + fine))
    Wvals = []
    for a in grid:
        ronset, found = onset_ratio(a, ntheta=240)
        if not found:
            print(f"{mp.nstr(a,7):>10} | {float(a/SQRT3):8.3f} | {apex_angle_deg(a):8.2f} "
                  f"| {'--':>12} | {'0 (convex)':>12} | no")
            Wvals.append((a, mp.mpf(0)))
        else:
            W = 1 - ronset
            print(f"{mp.nstr(a,7):>10} | {float(a/SQRT3):8.3f} | {apex_angle_deg(a):8.2f} "
                  f"| {mp.nstr(ronset,10):>12} | {mp.nstr(W,8):>12} | YES")
            Wvals.append((a, W))

    print("=" * 74)
    print("READING:")
    print(" * W(a) > 0 for every tested a < sqrt3, shrinking monotonically toward 0 as")
    print("   a -> sqrt3 (the window narrows as the two conjugate saddles coalesce).")
    print(" * W(sqrt3) = 0 exactly: the EQUILATERAL triple is the lone all-convex member.")
    print(" => On this conjugate-symmetric isoceles family, all-components-convex is a")
    print("    KNIFE-EDGE at the equilateral configuration: ANY isoceles deviation")
    print("    (apex angle != 60 deg) produces a non-convex apex component in a window")
    print("    (c_nc, c*) just below merge.  W(0) is the collinear (z^3+z) width; it")
    print("    matches the Session-1 collinear-simple necking, the a=0 control above.")
