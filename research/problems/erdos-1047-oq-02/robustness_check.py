#!/usr/bin/env python3
"""
Robustness / resolution check for the curvature-verified non-convex Pommerenke
component, to rule out saddle-point numerical noise.

Strategy:
 - Pick a ROBUST case far from numerical danger: large k, large a, so the
   working c and the curve radius are O(0.1-1), grad g not tiny.
 - Re-evaluate worst curvature at several grid resolutions; a genuine geometric
   non-convexity is resolution-stable, saddle noise is not.
 - Also verify the marginal k=3,4 onset and report whether they survive.
 - Independent cross-check: parametrize the component-around-0 boundary directly
   by tracing r(theta) via 1-D root finding of |f(r e^{i theta})|=c (no grid, no
   contour), then test polar-curve convexity  r^2 + 2 r'^2 - r r'' >= 0.
"""
import numpy as np
from scipy.optimize import brentq

def f_abs(z, k, a):
    return abs(z)**k * abs(z - a)

def radius_at(theta, c, k, a, rmax):
    # solve |f(r e^{i th})| = c for the inner (component-around-0) branch
    g = lambda r: f_abs(r*np.exp(1j*theta), k, a) - c
    # f_abs(0)=0 < c ; increase r until exceeds c (first crossing = component-around-0 boundary)
    rs = np.linspace(1e-6, rmax, 4000)
    vals = np.array([g(r) for r in rs])
    sign = np.sign(vals)
    idx = np.where(np.diff(sign) > 0)[0]  # - to +
    if len(idx) == 0:
        return None
    i = idx[0]
    return brentq(g, rs[i], rs[i+1])

def polar_convexity(c, k, a, rmax, N=2000):
    th = np.linspace(0, 2*np.pi, N, endpoint=False)
    r = np.array([radius_at(t, c, k, a, rmax) for t in th])
    if any(v is None for v in r):
        return None, None, None
    r = np.array(r, dtype=float)
    dt = th[1]-th[0]
    rp = np.gradient(r, dt)
    rpp = np.gradient(rp, dt)
    conv = r**2 + 2*rp**2 - r*rpp     # >=0 everywhere  <=>  convex
    i = np.argmin(conv)
    return float(conv.min()), float(th[i]/np.pi), float(r.max()/r.min())

def find_cstar(k, a, rmax):
    # merge when component-around-0 reaches the saddle on segment (0,a): real axis dip
    # saddle value: max over r in (0,a) of f_abs(r,k,a) along positive real axis is a local
    # min of |f| between roots -> that's the saddle barrier height.
    rs = np.linspace(1e-4, a-1e-4, 20000)
    vals = rs**k * np.abs(rs - a)
    return vals.max()  # peak between the two roots = barrier = merge threshold c*

if __name__ == "__main__":
    print("INDEPENDENT POLAR-TRACE convexity test (no grid / no contour):")
    print("  conv_min < 0  <=>  component-around-0 is NON-CONVEX")
    print(f"{'k':>2} {'a':>4} {'c/c*':>6} {'c*':>10} {'c':>10} {'conv_min':>11} {'dimple/pi':>9} {'r_ratio':>7}")
    for (k, a) in [(3,1.0),(4,1.0),(5,1.0),(6,1.3),(8,1.3),(10,1.3)]:
        cstar = find_cstar(k, a, 1.6*a)
        for frac in [0.90, 0.97, 0.999]:
            c = cstar*frac
            cm, dimp, rr = polar_convexity(c, k, a, 1.7*a)
            if cm is None:
                print(f"{k:>2} {a:>4} {frac:>6} {cstar:>10.5f} {c:>10.5f}   (open/merged)")
            else:
                flag = " NON-CONVEX" if cm < -1e-4 else ""
                print(f"{k:>2} {a:>4} {frac:>6} {cstar:>10.5f} {c:>10.5f} {cm:>11.5f} {dimp:>9.3f} {rr:>7.3f}{flag}")
