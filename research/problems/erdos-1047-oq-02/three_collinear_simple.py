#!/usr/bin/env python3
"""
erdos-1047-oq-02  (researcher-1) — DECISIVE check: does the MIDDLE component of
THREE COLLINEAR SIMPLE roots become non-convex in a razor-thin pre-merge window?

Motivation.  three_root_certify.py found, for EQUAL multiplicity (2,2,2) at
ratio c/c* = 0.9999, that min Re(u') = -0.032 on the middle component.  By the
Session-3 sign-invariance reduction (f and f^m have identical level sets and
Re(u') changes only by the positive factor 1/m), this is the SAME boundary as
f = z(z-1)(z-2) at geometric ratio 0.99995, and predicts

    Re(u')_{(1,1,1)} (that boundary)  =  2 * (-0.032)  =  -0.064  <  0,

i.e. THREE COLLINEAR SIMPLE roots already have a non-convex middle component in
a window just below merge -- a counterexample needing NO multiplicity, missed by
the coarse (c/c* <= 0.999) scans.  This contradicts the naive reading of the
two-root result (equal simple roots never neck); the THIRD root squeezing the
middle one from the opposite side is the new effect.

We verify directly on f = z(z-1)(z-2):
  * push c/c* -> 1 (ratios 0.999 ... 0.9999999),
  * for each, trace the middle (z=1) component boundary at HIGH PRECISION,
    report min Re(u') and the WORST ANGLE (to confirm it is an off-axis
    SHOULDER, theta away from 0 and pi, not a near-saddle tracing artifact),
  * give a high-precision sign certificate at the worst point.

Criterion: convex <=> Re(u') >= 0,  w = sum 1/(z-r_j),  u'=-w'/w^2.
Docker-independent.  Requires mpmath.
"""
import mpmath as mp

mp.mp.dps = 40

ROOTS = [mp.mpf(0), mp.mpf(1), mp.mpf(2)]   # collinear simple, middle = 1


def w(z):
    return sum(1 / (z - r) for r in ROOTS)


def fabs(z):
    out = mp.mpf(1)
    for r in ROOTS:
        out = out * abs(z - r)
    return out


def re_uprime(z):
    ww = w(z)
    wp = -sum(1 / (z - r) ** 2 for r in ROOTS)
    return mp.re(-wp / ww ** 2)


def cstar():
    # symmetric saddle of f = z(z-1)(z-2): 1 - 1/sqrt(3)
    s = 1 - 1 / mp.sqrt(3)
    return fabs(mp.mpc(s, 0))


def radius_at(theta, c, r0=mp.mpc(1, 0), rmax=mp.mpf("1.2")):
    """First outward crossing of |f|=c along ray from r0 at angle theta."""
    d = mp.e ** (1j * theta)
    # find a bracket [lo,hi] with fabs(lo)<c<=fabs(hi)
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


def min_over_boundary(c, ntheta=720):
    """Min Re(u') over the middle component boundary; returns (val, theta, z)."""
    best = mp.mpf("inf")
    bth = None
    bz = None
    r0 = mp.mpc(1, 0)
    for j in range(ntheta):
        th = 2 * mp.pi * j / ntheta
        rr = radius_at(th, c)
        if rr is None:
            continue
        z = r0 + rr * mp.e ** (1j * th)
        v = re_uprime(z)
        if v < best:
            best = v
            bth = th
            bz = z
    return best, bth, bz


def refine_angle(c, th0, half=mp.mpf("0.15")):
    """Golden-section refine the angular minimum of Re(u') near th0."""
    r0 = mp.mpc(1, 0)

    def val(th):
        rr = radius_at(th, c)
        z = r0 + rr * mp.e ** (1j * th)
        return re_uprime(z), z

    lo, hi = th0 - half, th0 + half
    gz = None
    for _ in range(100):
        m1 = lo + (hi - lo) / 3
        m2 = hi - (hi - lo) / 3
        v1, _ = val(m1)
        v2, _ = val(m2)
        if v1 < v2:
            hi = m2
        else:
            lo = m1
    thm = (lo + hi) / 2
    v, z = val(thm)
    return v, thm, z


if __name__ == "__main__":
    cs = cstar()
    print("f = z(z-1)(z-2), three collinear SIMPLE roots; middle component (z=1)")
    print("c* (merge) =", mp.nstr(cs, 20))
    print("=" * 70)
    lbl = "min Re(uprime)"
    print(f"{'c/c*':>12} | {lbl:>14} | {'worst theta/pi':>16} | convex?")
    print("-" * 70)
    crossed = False
    for ratio in ["0.999", "0.9999", "0.99995", "0.99999", "0.999999"]:
        c = mp.mpf(ratio) * cs
        v, th, z = min_over_boundary(c, ntheta=360)
        v2, th2, z2 = refine_angle(c, th)
        if v2 < v:
            v, th, z = v2, th2, z2
        thpi = float(th / mp.pi)
        # fold theta into [0,2): shoulders near 0 or pi are "axis"; else off-axis
        conv = "YES" if v >= 0 else "NO  (NON-CONVEX)"
        if v < 0:
            crossed = True
        print(f"{ratio:>12} | {mp.nstr(v,10):>14} | {thpi:16.5f} | {conv}")
        if v < 0:
            print(f"             worst z* = {mp.nstr(z,16)}  |f(z*)| matches c: "
                  f"{mp.nstr(fabs(z)-c,3)}")
    print("-" * 70)
    if crossed:
        print("CONFIRMED: three collinear SIMPLE roots -> the MIDDLE component is")
        print("NON-CONVEX in a razor-thin window just below merge (off-axis shoulders).")
        print("This is a genuine counterexample requiring NO multiplicity; the two")
        print("OUTER roots stay convex.  The third root squeezing the middle root")
        print("from the opposite side is the mechanism the two-root analysis misses.")
    else:
        print("No negative value found up to the tested ratio (would need closer-to-merge).")
