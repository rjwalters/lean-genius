#!/usr/bin/env python3
"""
erdos-1047-oq-02  (researcher-1) — CONTROL for three_collinear_simple.py.

The three-collinear-simple finding (middle component non-convex just below
merge) is surprising, so we validate the SAME boundary tracer against a case
with a KNOWN answer: f = z(z-1), two simple roots.  Session 3 PROVED in closed
form (8c^2 - 6c + 1, knowledge.md) that for the separated regime c < c* = 1/4
BOTH components are CONVEX, with non-convexity only in the merged regime
1/4 < c < 1/2.  So the tracer MUST return min Re(u') >= 0 for c < 1/4, right up
to merge.  If it does (two-root convex) while three-collinear returns negative,
the three-root necking is real, not a near-saddle artifact.

We also re-confirm the three-collinear-simple negative at one ratio with the
identical code path, side by side.
"""
import mpmath as mp

mp.mp.dps = 40


def make(roots):
    R = [mp.mpf(r) if not isinstance(r, complex) else mp.mpc(r.real, r.imag) for r in roots]

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


def radius_at(fabs, r0, theta, c, rmax=mp.mpf("1.2")):
    d = mp.e ** (1j * theta)
    lo = mp.mpf("1e-12")
    hi = None
    prev = lo
    steps = 4000
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


def min_boundary(fabs, reup, r0, c, ntheta=720):
    best = mp.mpf("inf")
    bz = None
    bth = None
    for j in range(ntheta):
        th = 2 * mp.pi * j / ntheta
        rr = radius_at(fabs, r0, th, c)
        if rr is None:
            continue
        z = r0 + rr * mp.e ** (1j * th)
        v = reup(z)
        if v < best:
            best, bz, bth = v, z, th
    return best, bz, bth


if __name__ == "__main__":
    print("CONTROL: identical tracer on known cases")
    print("=" * 64)

    # --- two simple roots z(z-1); component around 0; c* = 1/4 (PROVEN convex) ---
    R, fabs, reup = make([0, 1])
    r0 = mp.mpc(0, 0)
    cstar2 = mp.mpf(1) / 4
    print("f = z(z-1)  [Session-3 PROOF: separated (c<1/4) is CONVEX]")
    print(f"  c* = {mp.nstr(cstar2,12)}")
    ok2 = True
    for ratio in ["0.99", "0.999", "0.9999", "0.99999", "0.999999"]:
        c = mp.mpf(ratio) * cstar2
        v, z, th = min_boundary(fabs, reup, r0, c)
        ok2 &= (v >= -mp.mpf("1e-12"))
        print(f"  c/c*={ratio:>9}: min Re(uprime) = {mp.nstr(v,10):>14}  "
              f"({'convex OK' if v >= -1e-12 else 'NEG -- tracer bug!'})")
    print(f"  -> {'tracer AGREES with proof (stays convex)' if ok2 else 'TRACER DISAGREES WITH PROOF'}")

    # --- three collinear simple z(z-1)(z-2); middle (z=1) (claim: necks) ---
    print()
    R, fabs, reup = make([0, 1, 2])
    r1 = mp.mpc(1, 0)
    cstar3 = fabs(mp.mpc(1 - 1 / mp.sqrt(3), 0))
    print("f = z(z-1)(z-2)  middle component z=1  [claim: NON-CONVEX near merge]")
    print(f"  c* = {mp.nstr(cstar3,12)}")
    neg3 = False
    for ratio in ["0.999", "0.9999", "0.99995", "0.99999"]:
        c = mp.mpf(ratio) * cstar3
        v, z, th = min_boundary(fabs, reup, r1, c)
        neg3 |= (v < 0)
        print(f"  c/c*={ratio:>9}: min Re(uprime) = {mp.nstr(v,10):>14}  "
              f"({'convex' if v >= 0 else 'NON-CONVEX'})  worst z={mp.nstr(z,10)}")
    print()
    print("=" * 64)
    if ok2 and neg3:
        print("VALID: tracer reproduces the PROVEN two-root convexity, yet finds a")
        print("genuine non-convex MIDDLE component for three collinear simple roots.")
        print("=> the three-root necking is real, not a near-saddle numerical artifact.")
    else:
        print("INCONCLUSIVE: control failed; re-examine the tracer.")
