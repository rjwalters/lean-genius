#!/usr/bin/env python3
"""
Map the NON-CONVEX WINDOW width vs root multiplicity for Pommerenke f=z^k(z-a).

For each k, find c_nc = smallest c at which the component-around-0 first becomes
non-convex (polar-trace convexity test), and report the relative window width
W(k) = (c* - c_nc)/c*  where c* is the merge threshold.

W(k) ~ 0  => non-convexity only at the instant of merging (not a robust separate
             counterexample)
W(k) >> 0 => a robust band of c with a non-convex SEPARATE component (genuine
             Erdos #1047 counterexample in the m-component regime).
"""
import numpy as np
from scipy.optimize import brentq

def f_abs(z, k, a):
    return abs(z)**k * abs(z - a)

def radius_at(theta, c, k, a, rmax):
    g = lambda r: f_abs(r*np.exp(1j*theta), k, a) - c
    rs = np.linspace(1e-7, rmax, 5000)
    vals = rs**k * np.abs(rs*np.exp(1j*theta) - a) - c
    sign = np.sign(vals)
    idx = np.where(np.diff(sign) > 0)[0]
    if len(idx) == 0:
        return None
    i = idx[0]
    return brentq(g, rs[i], rs[i+1])

def conv_min(c, k, a, rmax, N=1500):
    th = np.linspace(0, 2*np.pi, N, endpoint=False)
    r = []
    for t in th:
        v = radius_at(t, c, k, a, rmax)
        if v is None:
            return None
        r.append(v)
    r = np.array(r)
    dt = th[1]-th[0]
    rp = np.gradient(r, dt); rpp = np.gradient(rp, dt)
    return float((r**2 + 2*rp**2 - r*rpp).min())

def cstar(k, a):
    rs = np.linspace(1e-5, a-1e-5, 50000)
    return float((rs**k * np.abs(rs - a)).max())

def window(k, a):
    cs = cstar(k, a)
    rmax = 1.8*a
    # bisect for c_nc in (lo, cs): convex below, nonconvex near cs
    lo, hi = 0.3*cs, cs*(1-1e-7)
    # ensure hi is nonconvex
    if conv_min(hi, k, a, rmax) >= 0:
        return cs, None, 0.0   # never nonconvex even at merge
    # ensure lo is convex
    if conv_min(lo, k, a, rmax) < 0:
        lo = 0.05*cs
    for _ in range(28):
        mid = 0.5*(lo+hi)
        cm = conv_min(mid, k, a, rmax)
        if cm is None or cm >= 0:
            lo = mid
        else:
            hi = mid
    c_nc = hi
    return cs, c_nc, (cs - c_nc)/cs

if __name__ == "__main__":
    print("Pommerenke z^k(z-a): non-convex window of the component around the mult-k root")
    print(f"{'k':>2} {'a':>4} {'c*':>10} {'c_nc':>10} {'W=(c*-c_nc)/c*':>15}")
    for a in [1.0, 1.3]:
        for k in [1, 2, 3, 4, 5, 6, 8, 10]:
            cs, c_nc, W = window(k, a)
            cncs = f"{c_nc:.6f}" if c_nc is not None else "   --   "
            print(f"{k:>2} {a:>4} {cs:>10.6f} {cncs:>10} {W*100:>13.3f}%")
        print()
