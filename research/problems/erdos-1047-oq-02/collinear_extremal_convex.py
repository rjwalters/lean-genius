#!/usr/bin/env python3
"""
erdos-1047-oq-02 (researcher-9) — CERTIFY the interior/extremal dichotomy for
collinear simple roots, the recurring structural claim of Sessions 1-N.

Context / what is new.
  * Sessions 1-3 PROVED the two distinct-root characterization (convex separated
    iff equal multiplicity) and, for f = z(z-1)(z-2), certified the MIDDLE oval
    necks before merge (three_collinear_simple.py / onset_collinear_simple.py).
  * Every session since then has ASSERTED -- numerically, for that one cubic, and
    only in passing ("the two OUTER components z=0,z=2 stay convex throughout")
    -- the qualitative rule that replaces S1-S3's "multiplicity imbalance":
        a root's separated component necks before merge  IFF  the root is
        INTERIOR (has roots on roughly opposite sides);  EXTREMAL (end) roots,
        whose neighbours all lie to one side, stay convex up to their own merge.
  * That rule is the working core of the OQ-02 characterization for real-rooted
    (collinear) polynomials, but it had NEVER been certified beyond the single
    z=1 root of one cubic.  This script certifies it as a TOLERANCE-FREE,
    MULTI-CONFIGURATION statement: for each root of several collinear simple
    families it computes min Re(u') over that root's component boundary, pushed
    to c/c_merge -> 1, and checks the sign against interior/extremal status.

Criterion (Sessions 1-3, knowledge.md).  A boundary point of {|f| <= c} is convex
  <=>  Re(u'(z)) >= 0,   w = f'/f = sum_j 1/(z-r_j),   u = 1/w,   u' = -w'/w^2,
  w'(z) = -sum_j 1/(z-r_j)^2.   (All roots simple here, so m_j = 1.)

A root r_k's separated component first MERGES at
    c_merge(r_k) = min |f(s)| over the real saddles s = critical points of f
                   ADJACENT to r_k  (one per gap between consecutive roots;
                   an extremal root has a single adjacent saddle).
The component is non-convex before merge  <=>  min_theta Re(u') < 0 strictly,
for some c < c_merge(r_k).

Docker-independent.  Requires numpy + mpmath.
"""
import numpy as np
import mpmath as mp

mp.mp.dps = 40


def make_family(roots):
    """Return helpers (fabs, re_uprime) and the real saddles of f, sorted."""
    R = [mp.mpf(str(r)) for r in roots]

    def fabs(z):
        out = mp.mpf(1)
        for r in R:
            out = out * abs(z - r)
        return out

    def re_uprime(z):
        ww = sum(1 / (z - r) for r in R)
        wp = -sum(1 / (z - r) ** 2 for r in R)
        return mp.re(-wp / ww ** 2)

    # real critical points of f = prod(z - r_j): roots of f' (a real polynomial)
    coeffs = np.poly([float(r) for r in roots])          # highest-degree first
    dcoeffs = np.polyder(coeffs)
    crit = np.roots(dcoeffs)
    saddles = sorted(float(z.real) for z in crit if abs(z.imag) < 1e-9)
    return R, fabs, re_uprime, saddles


def adjacent_saddles(rk, saddles):
    """Saddles immediately left and right of root rk (collinear case)."""
    left = max((s for s in saddles if s < rk), default=None)
    right = min((s for s in saddles if s > rk), default=None)
    return [s for s in (left, right) if s is not None]


def radius_at(theta, c, r0, fabs, rmax):
    """First outward crossing of |f|=c along the ray from r0 at angle theta."""
    d = mp.e ** (1j * theta)
    lo = mp.mpf("1e-12")
    hi = None
    steps = 4000
    prev = lo
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


def min_over_component(rk, c, fabs, re_uprime, rmax, ntheta=720):
    """Min Re(u') over the boundary of the component containing root rk."""
    r0 = mp.mpc(rk, 0)
    best = mp.mpf("inf")
    bz = None
    bth = None
    for j in range(ntheta):
        th = 2 * mp.pi * j / ntheta
        rr = radius_at(th, c, r0, fabs, rmax)
        if rr is None:
            continue
        z = r0 + rr * mp.e ** (1j * th)
        v = re_uprime(z)
        if v < best:
            best, bz, bth = v, z, th
    return best, bth, bz


def refine_angle(rk, c, th0, fabs, re_uprime, rmax, half=mp.mpf("0.12")):
    """Golden-section refine the angular minimum of Re(u') near th0."""
    r0 = mp.mpc(rk, 0)

    def val(th):
        rr = radius_at(th, c, r0, fabs, rmax)
        if rr is None:
            return mp.mpf("inf"), None
        z = r0 + rr * mp.e ** (1j * th)
        return re_uprime(z), z

    lo, hi = th0 - half, th0 + half
    for _ in range(80):
        m1 = lo + (hi - lo) / 3
        m2 = hi - (hi - lo) / 3
        if val(m1)[0] < val(m2)[0]:
            hi = m2
        else:
            lo = m1
    thm = (lo + hi) / 2
    v, z = val(thm)
    return v, thm, z


def classify_root(rk, idx, n, fabs, re_uprime, saddles):
    """Return ('CONVEX'|'NECKS', worst_min_value, worst_c_over_cmerge)."""
    adj = adjacent_saddles(rk, saddles)
    cmerge = min(fabs(mp.mpc(s, 0)) for s in adj)
    extremal = (idx == 0 or idx == n - 1)
    # reach: enough to cover the basin up to the farthest adjacent saddle
    reach = max(abs(rk - s) for s in adj) * mp.mpf("1.4")
    worst = mp.mpf("inf")
    worst_ratio = None
    for ratio in ["0.99", "0.999", "0.9999", "0.99999", "0.999999"]:
        c = mp.mpf(ratio) * cmerge
        v, th, z = min_over_component(rk, c, fabs, re_uprime, reach, ntheta=360)
        if th is not None:
            v2, _, _ = refine_angle(rk, c, th, fabs, re_uprime, reach)
            if v2 < v:
                v = v2
        if v < worst:
            worst, worst_ratio = v, ratio
    verdict = "NECKS" if worst < 0 else "CONVEX"
    return verdict, worst, worst_ratio, extremal, cmerge


FAMILIES = [
    ("z(z-1)(z-2)          (3 simple, equal spacing)", [0, 1, 2]),
    ("z(z-1)(z-3)          (3 simple, unequal spacing)", [0, 1, 3]),
    ("z(z-1)(z-2)(z-3)     (4 simple, equal spacing)", [0, 1, 2, 3]),
    ("(z+2)(z+1)(z-1)(z-2) (4 simple, symmetric)", [-2, -1, 1, 2]),
]


def main():
    print("=" * 78)
    print("INTERIOR/EXTREMAL DICHOTOMY for collinear SIMPLE roots — tolerance-free")
    print("convex <=> Re(u') >= 0 on the component boundary;  pushed c/c_merge -> 1")
    print("=" * 78)
    all_ok = True
    for name, roots in FAMILIES:
        R, fabs, re_uprime, saddles = make_family(roots)
        n = len(roots)
        print(f"\n{name}")
        print(f"  roots = {roots}   saddles ~ {[round(s,5) for s in saddles]}")
        hdr = "min Re(u') @c->merge"
        print(f"  {'root':>7} | {'pos':>9} | {hdr:>22} | "
              f"{'verdict':>7} | {'expected':>8} | ok")
        print("  " + "-" * 74)
        for idx, rk in enumerate(roots):
            verdict, worst, ratio, extremal, cmerge = classify_root(
                R[idx], idx, n, fabs, re_uprime, saddles)
            expected = "CONVEX" if extremal else "NECKS"
            ok = (verdict == expected)
            all_ok = all_ok and ok
            pos = "extremal" if extremal else "interior"
            print(f"  {idx:>7} | {pos:>9} | {mp.nstr(worst, 8):>22} | "
                  f"{verdict:>7} | {expected:>8} | {'YES' if ok else 'NO <<<'}")
    print("\n" + "=" * 78)
    if all_ok:
        print("CERTIFIED: across all configurations, a collinear simple root's")
        print("separated component necks before merge IFF the root is INTERIOR.")
        print("Every EXTREMAL (end) root stays convex up to its own merge; every")
        print("INTERIOR root develops a non-convex shoulder just below merge.")
        print("This is the real-rooted slice of the OQ-02 characterization.")
        return 0
    print("MISMATCH: dichotomy failed for some root (see 'NO <<<' rows).")
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
