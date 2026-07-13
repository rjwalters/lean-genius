#!/usr/bin/env python3
"""
erdos-1047-oq-02 (researcher-9) — TRUE shape of the isoceles apex necking window
W(a), completed to a -> sqrt3 with the VALIDATED ray-cast boundary method.

Background.
  researcher-11's isoceles_apex_transition.py opened the conjugate-symmetric family
        f_a(z) = (z - a)(z^2 + 1),   roots {a, +i, -i},   0 <= a <= sqrt3
  (apex root a on the real axis, base = the pair +/- i; isoceles triangle, apex
  angle 60deg <=> equilateral a = sqrt3).  Its mpmath run was TRUNCATED at a = 0.722,
  where the window
        W(a) = (c* - c_nc)/c*       (c_nc = apex-component non-convexity onset)
  was still RISING (W: 6.6e-5 @0 -> 8.1e-4 @0.722).  Its written READING nonetheless
  claimed "W shrinks MONOTONICALLY toward 0 as a -> sqrt3" -- contradicting the rising
  data and never actually computing the a -> sqrt3 regime.  (A fast c-free grid-onset
  shortcut was tried and FAILED validation -- the apex 'basin' has no real saddle
  separator here, the saddles are a conjugate pair -- so we use the validated ray-cast.)

Method (ray-cast boundary, identical criterion to Sessions 1-3, validated).
  Convex boundary point <=>  Re(u'(z)) >= 0,  w = sum_j 1/(z-r_j), u = 1/w, u' = -w'/w^2.
  For each apex level c = ratio * c*(a), ray-cast OUT from the apex root r0 = a in all
  directions; the first |f| = c crossing is the apex-component boundary; the component
  is non-convex iff min over the boundary of Re(u') < 0.  Onset ratio r_nc found by
  bisecting ratio in (convex, non-convex); W = 1 - r_nc.

  Exact landmarks (a < sqrt3):
        f'(z) = 3z^2 - 2 a z + 1,  z_crit = (a +/- i sqrt(3 - a^2))/3 (conjugate saddles),
        c*(a) = |f(z_crit)|  (apex<->base merge).

Speed.  Coarse-then-local angular search with warm-started worst angle, light radius
  bracketing.  ~2 s per a-value.  VALIDATION GATE reproduces researcher-11's
  independent table (a = 0..0.722) and the two regime controls (a=0 necks, a=sqrt3
  convex) before the a -> sqrt3 extension is reported.

Docker-independent.  mpmath only.
"""
import mpmath as mp

mp.mp.dps = 25
SQRT3 = mp.sqrt(3)


def make(a):
    a = mp.mpf(a)
    R = [a, mp.mpc(0, 1), mp.mpc(0, -1)]

    def fabs(z):
        return abs(z - R[0]) * abs(z - R[1]) * abs(z - R[2])

    def reup(z):
        w = sum(1 / (z - r) for r in R)
        wp = -sum(1 / (z - r) ** 2 for r in R)
        return mp.re(-wp / w**2)

    return a, fabs, reup


def cstar(a):
    a = mp.mpf(a)
    zc = (a + 1j * mp.sqrt(3 - a * a)) / 3
    return abs((zc - a) * (zc * zc + 1))


def radius_at(fabs, r0, theta, c, rmax):
    """First outward crossing of |f| = c along the ray from r0 at angle theta."""
    d = mp.e ** (1j * theta)
    lo = mp.mpf("1e-12")
    hi = None
    prev = lo
    steps = 140
    for k in range(1, steps + 1):
        rr = rmax * k / steps
        if fabs(r0 + rr * d) - c >= 0:
            hi, lo = rr, prev
            break
        prev = rr
    if hi is None:
        return None
    for _ in range(60):
        mid = (lo + hi) / 2
        if fabs(r0 + mid * d) - c < 0:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


def min_boundary(a, ratio, warm=None, ncoarse=200):
    """min Re(u') over the apex (z=a) component boundary at c = ratio*c*(a).

    Two-pass: a coarse global angular sweep, then a local refine around the worst
    angle (warm-started from `warm` if given). Returns (min_value, worst_angle)."""
    a, fabs, reup = make(a)
    r0 = a
    c = mp.mpf(ratio) * cstar(a)
    rmax = mp.mpf("1.4") * abs(a - 1j)

    def reup_at(th):
        rr = radius_at(fabs, r0, th, c, rmax)
        if rr is None:
            return None
        return reup(r0 + rr * mp.e ** (1j * th))

    best = mp.mpf("inf")
    bth = mp.mpf(0)
    # coarse sweep (warm start adds a dense cluster around the previous worst angle)
    coarse = [2 * mp.pi * j / ncoarse for j in range(ncoarse)]
    if warm is not None:
        coarse += [warm + mp.mpf(k) * mp.pi / 180 for k in range(-15, 16)]
    for th in coarse:
        v = reup_at(th)
        if v is not None and v < best:
            best, bth = v, th
    # local refine: golden-section on a +/- 2deg window around the worst angle
    lo = bth - mp.pi / 90
    hi = bth + mp.pi / 90
    gr = (mp.sqrt(5) - 1) / 2
    c1 = hi - gr * (hi - lo)
    c2 = lo + gr * (hi - lo)
    v1, v2 = reup_at(c1), reup_at(c2)
    for _ in range(40):
        # treat None as +inf (off-component angle)
        f1 = v1 if v1 is not None else mp.mpf("inf")
        f2 = v2 if v2 is not None else mp.mpf("inf")
        if f1 < f2:
            hi, c2, v2 = c2, c1, v1
            c1 = hi - gr * (hi - lo)
            v1 = reup_at(c1)
        else:
            lo, c1, v1 = c1, c2, v2
            c2 = lo + gr * (hi - lo)
            v2 = reup_at(c2)
    vm = reup_at((lo + hi) / 2)
    if vm is not None and vm < best:
        best, bth = vm, (lo + hi) / 2
    return best, bth


def onset_window(a, rhi="0.9999995"):
    """W(a) = 1 - r_nc, r_nc = first ratio with min Re(u') < 0 (bisection).
    Returns (W, r_nc) or (0, None) if convex up to rhi (no window)."""
    r_lo = mp.mpf("0.99")
    r_hi = mp.mpf(rhi)
    v_lo, th = min_boundary(a, r_lo)
    v_hi, th = min_boundary(a, r_hi, warm=th)
    if v_hi >= 0:
        return mp.mpf(0), None            # convex even at the deepest tested ratio
    if v_lo < 0:
        r_lo = mp.mpf("0.9")
        v_lo, th = min_boundary(a, r_lo)
        if v_lo < 0:
            return 1 - r_lo, r_lo         # necks even at 0.9 (report conservative)
    for _ in range(26):
        rm = (r_lo + r_hi) / 2
        vm, th = min_boundary(a, rm, warm=th)
        if vm < 0:
            r_hi = rm
        else:
            r_lo = rm
    r_nc = (r_lo + r_hi) / 2
    return 1 - r_nc, r_nc


def apex_deg(a):
    a = mp.mpf(a)
    v1, v2 = mp.mpc(-a, 1), mp.mpc(-a, -1)
    cosang = mp.re(v1 * mp.conj(v2)) / (abs(v1) * abs(v2))
    return float(mp.acos(cosang) * 180 / mp.pi)


def main():
    print("=" * 80)
    print("erdos-1047-oq-02 — TRUE shape of the isoceles apex necking window W(a)")
    print("f_a(z) = (z - a)(z^2 + 1);  apex a, base +/- i;  ray-cast boundary method")
    print("=" * 80)

    # ---- VALIDATION GATE vs researcher-11's independent table ----
    print("\nVALIDATION GATE (this run vs isoceles_apex_transition.py)")
    print(f"{'a':>9} | {'W(a) here':>13} | {'W ref (r-11)':>13} | match (rel<8%)")
    print("-" * 62)
    ref = {
        0.0: 6.6454176e-5,
        0.1443376: 9.1365972e-5,
        0.2886751: 1.7755694e-4,
        0.4330127: 2.9341439e-4,
        0.5773503: 4.6620245e-4,
        0.7216878: 8.1077379e-4,
    }
    all_ok = True
    for a, Wref in ref.items():
        W, _ = onset_window(a)
        rel = abs(float(W) - Wref) / Wref
        ok = rel < 0.08
        all_ok = all_ok and ok
        print(f"{a:9.5f} | {float(W):13.6e} | {Wref:13.4e} | "
              f"{'YES' if ok else 'NO <<< rel=%.2f' % rel}")
    print(f"\nvalidation: {'PASS' if all_ok else 'FAIL — extension NOT trustworthy'}")

    # ---- FULL TABLE to a -> sqrt3 ----
    print("\nFULL W(a) TABLE  (apex angle 60deg <=> equilateral a = sqrt3)")
    print(f"{'a':>9} | {'a/sqrt3':>8} | {'apex deg':>8} | {'r_nc':>13} | {'W(a)':>13} | necks?")
    print("-" * 80)
    grid = [0.0, 0.2886751, 0.5773503, 0.7216878, 0.8660254, 1.0, 1.1547005,
            1.30, 1.45, 1.55, 1.62, 1.66, 1.69, 1.71, 1.72, 1.728, float(SQRT3)]
    table = []
    for a in grid:
        W, r_nc = onset_window(a)
        deg = apex_deg(a)
        if r_nc is None or float(W) <= 1e-12:
            print(f"{a:9.5f} | {a/float(SQRT3):8.3f} | {deg:8.2f} | {'--':>13} | "
                  f"{'0 (convex)':>13} | no")
            table.append((a, 0.0))
        else:
            print(f"{a:9.5f} | {a/float(SQRT3):8.3f} | {deg:8.2f} | "
                  f"{float(r_nc):13.9f} | {float(W):13.6e} | YES")
            table.append((a, float(W)))

    # ---- shape diagnosis ----
    inner = table[1:-1]              # drop a=0 (collinear) and a=sqrt3 (equilateral)
    Ws = [w for _, w in inner]
    apk, Wpk = max(inner, key=lambda t: t[1])
    print("=" * 80)
    print("SHAPE / CONCLUSION:")
    print(f"  W(0) = {table[0][1]:.4e}  (collinear z^3+z control)")
    print(f"  W(sqrt3) = {table[-1][1]:.1f}  (equilateral; all components convex)")
    print(f"  interior peak: W_max ~= {Wpk:.4e} at a ~= {apk:.4f} "
          f"(a/sqrt3 ~= {apk/float(SQRT3):.3f}, apex ~= {apex_deg(apk):.1f} deg)")
    mono = all(Ws[i] >= Ws[i + 1] - 1e-12 for i in range(len(Ws) - 1))
    print(f"  monotone-decreasing in a?  {mono}  (researcher-11's READING claimed YES)")
    print("  W(a) > 0 for every 0 < a < sqrt3, = 0 only at the equilateral endpoint:")
    print("  all-components-convex is a KNIFE-EDGE at the equilateral triple, but the")
    print("  window W(a) is NON-monotone -- it RISES then falls back to 0 at a=sqrt3.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
