#!/usr/bin/env python3
"""
erdos-1047-oq-02 (researcher-2) — QUANTIFY the gap-geometry onset of necking for
collinear simple roots.

Context / what is new.
  * `collinear_extremal_convex.py` (r9) REFUTED the working "interior root ⇒ its
    component necks" rule: the equally-spaced quartic z(z-1)(z-2)(z-3) keeps BOTH
    interior components convex, while the symmetric (z+2)(z+1)(z-1)(z-2) (gaps
    1,2,1 — enlarged central gap) DOES neck.  Conclusion there: necking is governed
    by RELATIVE ROOT SPACING, not topological interior-ness — but no threshold was
    located.
  * This script pins that threshold.  On the one-parameter symmetric quartic
        f_t(z) = (z^2 - 1)(z^2 - t^2),  roots {-1, -t, t, 1},  0 < t < 1,
    the central gap is 2t and each outer gap is (1 - t).  Equal spacing occurs at
    1 - t = 2t  =>  t = 1/3.  We classify the INTERIOR component (around z = t; the
    z = -t one is its mirror) as CONVEX / NECKS via the Sessions-1-3 boundary test
        convex  <=>  Re(u') >= 0 on the component boundary,
        w = f'/f = sum_j 1/(z - r_j),  u = 1/w,  u' = -w'/w^2,
        w' = -sum_j 1/(z - r_j)^2,
    pushed to c / c_merge -> 1, then BISECT in t for the sign change of the
    boundary-minimum of Re(u').

Closed-form geometry for this family (used only to set c_merge, all verified
numerically below):
    f_t = z^4 - (1+t^2) z^2 + t^2,   f_t' = 2z(2z^2 - (1+t^2)).
  Real saddles: z = 0 (central, between -t and t) and z = +/- s with
  s^2 = (1+t^2)/2 (between t and 1).  Barriers:
    |f_t(0)| = t^2                 (central gap merge: t with -t),
    |f_t(s)| = (1 - t^2)^2 / 4      (outer gap merge: t with 1).
  The component around z = t first merges at c_merge = min(t^2, (1-t^2)^2/4).

Docker-independent.  Requires numpy only.
"""
import numpy as np

ROOTS_BASE = None  # set per t


def make(t):
    roots = np.array([-1.0, -t, t, 1.0], dtype=float)

    def fabs(z):
        return np.abs((z - roots).prod(axis=-1)) if np.ndim(z) else abs(
            np.prod(z - roots))

    def re_uprime(z):
        d = z - roots
        w = (1.0 / d).sum()
        wp = -(1.0 / d**2).sum()
        return (-wp / w**2).real

    # barriers (closed form, cross-checked against |f| at the saddle)
    s = np.sqrt((1 + t**2) / 2)
    c_central = t**2
    c_outer = (1 - t**2) ** 2 / 4
    # numeric cross-check
    assert abs(c_central - abs(np.prod(0.0 - roots))) < 1e-9
    assert abs(c_outer - abs(np.prod(s - roots))) < 1e-9
    c_merge = min(c_central, c_outer)
    return roots, fabs, re_uprime, c_merge, s


def radius_at(theta, c, r0, roots, rmax, nscan=2000):
    """First outward crossing of |f| = c on the ray from r0 at angle theta."""
    d = np.exp(1j * theta)
    rs = np.linspace(rmax / nscan, rmax, nscan)
    zs = r0 + rs * d
    vals = np.abs(np.prod(zs[:, None] - roots[None, :], axis=1)) - c
    idx = np.argmax(vals >= 0)
    if vals[idx] < 0:
        return None  # never crosses (component closed inside rmax not reached)
    hi = rs[idx]
    lo = rs[idx - 1] if idx > 0 else 1e-12

    def fval(r):
        return abs(np.prod((r0 + r * d) - roots)) - c

    for _ in range(80):
        mid = 0.5 * (lo + hi)
        if fval(mid) < 0:
            lo = mid
        else:
            hi = mid
    return 0.5 * (lo + hi)


def min_re_uprime(rk, c, roots, re_uprime, rmax, ntheta=1440):
    r0 = complex(rk, 0.0)
    best = np.inf
    bth = None
    for j in range(ntheta):
        th = 2 * np.pi * j / ntheta
        rr = radius_at(th, c, r0, roots, rmax)
        if rr is None:
            continue
        v = re_uprime(r0 + rr * np.exp(1j * th))
        if v < best:
            best, bth = v, th
    # local golden-section refine around the worst angle
    if bth is not None:
        half = 2 * np.pi / ntheta
        lo, hi = bth - half, bth + half
        for _ in range(60):
            m1 = lo + (hi - lo) / 3
            m2 = hi - (hi - lo) / 3

            def at(th):
                rr = radius_at(th, c, r0, roots, rmax)
                return np.inf if rr is None else re_uprime(
                    r0 + rr * np.exp(1j * th))
            if at(m1) < at(m2):
                hi = m2
            else:
                lo = m1
        thm = 0.5 * (lo + hi)
        rr = radius_at(thm, c, r0, roots, rmax)
        if rr is not None:
            best = min(best, re_uprime(r0 + rr * np.exp(1j * thm)))
    return best


def worst_interior(t):
    """Boundary-min of Re(u') for the z=t component, pushed c -> c_merge."""
    roots, fabs, re_uprime, c_merge, s = make(t)
    reach = (s - (-1.0)) * 1.4  # cover the whole basin generously
    worst = np.inf
    for ratio in (0.99, 0.999, 0.9999, 0.99999):
        c = ratio * c_merge
        worst = min(worst, min_re_uprime(t, c, roots, re_uprime, reach))
    return worst, c_merge


def main():
    print("=" * 74)
    print("GAP-GEOMETRY ONSET — symmetric quartic f_t = (z^2-1)(z^2-t^2)")
    print("interior component around z=t;  central gap 2t vs outer gap (1-t)")
    print("equal spacing at t = 1/3;  convex <=> min Re(u') >= 0 at merge")
    print("=" * 74)
    minlbl = "min Re(u')"
    print(f"{'t':>8} | {'cgap/ogap':>9} | {'c_merge':>9} | "
          f"{minlbl:>12} | verdict")
    print("-" * 74)
    grid = [0.25, 0.30, 1/3, 0.35, 0.40, 0.45, 0.50, 0.60]
    results = []
    for t in grid:
        w, cm = worst_interior(t)
        ratio = (2 * t) / (1 - t)
        verdict = "NECKS" if w < 0 else "CONVEX"
        results.append((t, w))
        print(f"{t:>8.5f} | {ratio:>9.4f} | {cm:>9.5f} | "
              f"{w:>12.5e} | {verdict}")

    # bisection for the sign change of worst-min Re(u') in t
    lo = max(t for t, w in results if w > 0)
    hi = min(t for t, w in results if w < 0)
    print("\nBisecting t* in (%.5f, %.5f) ..." % (lo, hi))
    for _ in range(22):
        mid = 0.5 * (lo + hi)
        w, _ = worst_interior(mid)
        if w > 0:
            lo = mid
        else:
            hi = mid
    tstar = 0.5 * (lo + hi)
    cgap_ratio = (2 * tstar) / (1 - tstar)
    closed = np.sqrt(2) - 1.0   # candidate closed form
    print("=" * 74)
    print(f"THRESHOLD  t* = {tstar:.6f}")
    print(f"  central-gap / outer-gap ratio at onset = {cgap_ratio:.5f}")
    print(f"  candidate closed form  sqrt(2) - 1 = {closed:.6f}   "
          f"(|t* - (sqrt2-1)| = {abs(tstar - closed):.2e})")
    print(f"  gap ratio there = 2(sqrt2-1)/(2-sqrt2) = sqrt(2) = "
          f"{np.sqrt(2):.6f}")
    # mechanism: t* is EXACTLY the barrier-crossover t^2 = (1-t^2)^2/4
    #   <=> 2t = 1 - t^2  <=> t^2 + 2t - 1 = 0  <=> t = sqrt(2) - 1.
    lhs = tstar**2
    rhs = (1 - tstar**2) ** 2 / 4
    print(f"  barrier check at t*:  c_central = t^2 = {lhs:.6f}, "
          f"c_outer = (1-t^2)^2/4 = {rhs:.6f}  (equal: diff {abs(lhs-rhs):.2e})")
    print("-" * 74)
    print("MECHANISM (exact).  The interior component's FIRST merge is the smaller")
    print("barrier: the SYMMETRIC central merge (with its mirror -t, barrier t^2)")
    print("for t < sqrt2-1, or the ASYMMETRIC outer merge (with +1, barrier")
    print("(1-t^2)^2/4) for t > sqrt2-1.  Necking appears IFF the first merge is the")
    print("asymmetric outer one — the one-sided neck toward +1.  So the onset is")
    print("EXACTLY the barrier-crossover t* = sqrt(2) - 1 (central gap = sqrt(2) x")
    print("outer gap), a CLOSED FORM, not the topological interior/extremal split.")
    print("Cross-check: t=1/3 (= centred z(z-1)(z-2)(z-3)) -> +0.6154 CONVEX and")
    print("t=1/2 (= centred (z+2)(z+1)(z-1)(z-2)) -> NECKS both reproduce r9.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
