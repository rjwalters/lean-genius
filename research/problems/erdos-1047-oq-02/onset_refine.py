#!/usr/bin/env python3
"""
Pin down the ONSET multiplicity k for non-convex separate components in
Pommerenke's family f(z)=z^k(z-a), and locate the dimple.

For each k, scan c across the ENTIRE 2-component regime (0, c*) and report the
most-negative convex-calibrated curvature found on the component around 0, plus
the argument (angle) of the dimple point. Uses the analytic complex-curvature
machinery from pommerenke_scan.py.
"""
import numpy as np
from scipy import ndimage
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from pommerenke_scan import make_g, curvature_on_curve, newton, find_merge


def worst_curv_around_zero(roots, mult, c, R, res=900):
    f, fp, fpp = make_g(roots, mult)
    xs = np.linspace(-R, R, res); ys = np.linspace(-R, R, res)
    X, Y = np.meshgrid(xs, ys); Z = X + 1j * Y
    G = np.abs(f(Z)) ** 2
    cs = plt.contour(X, Y, G, levels=[c])
    a = roots[1]
    best = (np.inf, None, None)
    ncomp = ndimage.label(G <= c)[1]
    for seg in cs.allsegs[0]:
        if len(seg) < 10:
            continue
        pts = seg[:, 0] + 1j * seg[:, 1]
        # is this the loop around 0? check it encircles 0 not a
        cen = pts.mean()
        if abs(cen - 0) > abs(cen - a):
            continue
        pts = newton(pts, f, fp, c)
        k = curvature_on_curve(pts, f, fp, fpp)
        i = np.nanargmin(k)
        if k[i] < best[0]:
            best = (float(k[i]), float(np.angle(pts[i])), float(abs(pts[i])))
    plt.close("all")
    return ncomp, best


def onset(k, a=1.0):
    roots = [0.0, a]; mult = [k, 1]
    R = max(1.6 * a, 1.3)
    cstar = find_merge(roots, mult, R, 2, 1e-10, (a ** k) * a * 0.95, res=600)
    worst = (np.inf, None, None)
    cw = None
    for frac in np.linspace(0.10, 0.995, 24):
        c = cstar * frac
        nc, b = worst_curv_around_zero(roots, mult, c, R)
        if nc < 2:
            continue
        if b[0] < worst[0]:
            worst = b; cw = c
    return cstar, cw, worst


if __name__ == "__main__":
    print("Pommerenke f(z)=z^k(z-a), a=1.0 : onset of non-convex SEPARATE component around 0")
    print("k = root multiplicity ; degree = k+1 ; dimple angle in units of pi (pi = far side from a)")
    for k in [3, 4, 5, 6, 7]:
        cstar, cw, (kmin, ang, rad) = onset(k, a=1.0)
        deg = k + 1
        verdict = "NON-CONVEX" if kmin < -1e-2 else "convex"
        angpi = ang / np.pi if ang is not None else None
        print(f"  k={k} (deg {deg}): c*={cstar:.5f}  worst_kappa={kmin:+.4f} at c={cw} "
              f"angle={angpi:.3f}*pi rad={rad:.4f}  -> {verdict}" if ang is not None
              else f"  k={k} (deg {deg}): c*={cstar:.5f} worst_kappa={kmin:+.4f} -> {verdict}")
