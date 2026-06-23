#!/usr/bin/env python3
"""
Boundary signed-curvature test for convexity of polynomial lemniscate components.

Erdős #1047 / OQ-02: characterize which polynomials f have ALL components of
{z : |f(z)| <= c} convex, in the regime where the sublevel set has exactly
m = (number of distinct roots) connected components (one per root).

WHY CURVATURE, NOT AREA-DEFECT:
A previous session used a convex-hull area-defect grid metric. That metric is
blind to sub-grid concavity (a slightly dented oval can have ~0 hull defect).
The correct, sensitive tool is the SIGNED CURVATURE of the boundary curve.

For g(x,y) = |f(x+iy)|^2 (a real polynomial, smooth, with grad g != 0 on the
boundary because |f|=c>0 there), the boundary of a component is the level set
{g = c}. The signed curvature, calibrated so a sublevel disk {g<=c} is convex
iff kappa >= 0 everywhere, is

    kappa = ( g_x^2 g_yy - 2 g_x g_y g_xy + g_y^2 g_xx ) / (g_x^2 + g_y^2)^{3/2}

Calibration check: for g = x^2+y^2 (a disk) the numerator = 8(x^2+y^2) > 0, so
kappa > 0 -- correct, a disk is convex.

A connected component K of {g<=c} is convex  <=>  kappa >= 0 on all of dK.
Equivalently min over dK of kappa is >= 0 (up to numerical tolerance).

The contour vertices produced by marching squares are pushed exactly onto
{g=c} by a few Newton steps along grad g before curvature is evaluated, so the
reported curvature is the EXACT analytic curvature at points that genuinely lie
on the level set -- no grid noise in the curvature value itself.
"""
import sys
import numpy as np
import sympy as sp
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from scipy import ndimage

x, y = sp.symbols("x y", real=True)


def build_g(coeffs):
    """coeffs = real coefficients of f, highest degree first. Returns g=|f|^2 and lambdified derivatives."""
    z = x + sp.I * y
    f = sum(sp.Rational(c) * z**(len(coeffs) - 1 - k) for k, c in enumerate(coeffs))
    f = sp.expand(f)
    g = sp.expand(sp.re(f) ** 2 + sp.im(f) ** 2)
    gx = sp.diff(g, x)
    gy = sp.diff(g, y)
    gxx = sp.diff(g, x, 2)
    gyy = sp.diff(g, y, 2)
    gxy = sp.diff(g, x, y)
    num = gx**2 * gyy - 2 * gx * gy * gxy + gy**2 * gxx
    den = (gx**2 + gy**2)
    funcs = {
        "g": sp.lambdify((x, y), g, "numpy"),
        "gx": sp.lambdify((x, y), gx, "numpy"),
        "gy": sp.lambdify((x, y), gy, "numpy"),
        "num": sp.lambdify((x, y), num, "numpy"),
        "den": sp.lambdify((x, y), den, "numpy"),
    }
    return funcs


def newton_to_level(funcs, px, py, c, steps=4):
    """Push (px,py) onto {g=c} along grad g."""
    for _ in range(steps):
        gv = funcs["g"](px, py) - c
        gx = funcs["gx"](px, py)
        gy = funcs["gy"](px, py)
        nrm2 = gx * gx + gy * gy
        if nrm2 < 1e-14:
            break
        px = px - gv * gx / nrm2
        py = py - gv * gy / nrm2
    return px, py


def kappa(funcs, px, py):
    den = funcs["den"](px, py)
    if den < 1e-14:
        return None
    return funcs["num"](px, py) / den ** 1.5


def count_components(funcs, c, R, res=600):
    """Number of connected components of {g<=c} on [-R,R]^2."""
    xs = np.linspace(-R, R, res)
    ys = np.linspace(-R, R, res)
    X, Y = np.meshgrid(xs, ys)
    G = funcs["g"](X, Y)
    mask = G <= c
    _, n = ndimage.label(mask)
    return n


def min_curvature(funcs, c, R, res=900):
    """Extract level set {g=c}, return per-loop minimum convex-calibrated curvature."""
    xs = np.linspace(-R, R, res)
    ys = np.linspace(-R, R, res)
    X, Y = np.meshgrid(xs, ys)
    G = funcs["g"](X, Y)
    cs = plt.contour(X, Y, G, levels=[c])
    loops = []
    # matplotlib >=3.8: allsegs
    segs = cs.allsegs[0]
    for seg in segs:
        if len(seg) < 8:
            continue
        ks = []
        for (px, py) in seg:
            rx, ry = newton_to_level(funcs, px, py, c)
            k = kappa(funcs, rx, ry)
            if k is not None:
                ks.append(k)
        if ks:
            loops.append((min(ks), max(ks), len(ks)))
    plt.close("all")
    return loops


def analyze(name, coeffs, c, R, expect):
    funcs = build_g(coeffs)
    ncomp = count_components(funcs, c, R)
    loops = min_curvature(funcs, c, R)
    print(f"\n=== {name} ===")
    print(f"  coeffs={coeffs}  c={c:.6f}  region components(grid)={ncomp}")
    overall_min = None
    for i, (kmin, kmax, npts) in enumerate(loops):
        flag = "NON-CONVEX" if kmin < -1e-3 else "convex"
        print(f"  loop {i}: min_kappa={kmin:+.5f}  max_kappa={kmax:+.5f}  pts={npts}  -> {flag}")
        overall_min = kmin if overall_min is None else min(overall_min, kmin)
    verdict = "ALL CONVEX" if (overall_min is not None and overall_min >= -1e-3) else "HAS NON-CONVEX COMPONENT"
    print(f"  VERDICT: {verdict}   (expected: {expect})")
    return verdict


def calibrate():
    # circle g=x^2+y^2, c=1 -> single convex loop, kappa ~ +1
    funcs = build_g([1, 0, 0])  # f=z^2? no. Use f=z: coeffs=[1,0]-> g=x^2+y^2
    funcs = build_g([1, 0])  # f(z)=z, g=|z|^2=x^2+y^2
    loops = min_curvature(funcs, 1.0, 2.0)
    print("CALIBRATION (unit circle, expect kappa ~ +1.0):")
    for (kmin, kmax, n) in loops:
        print(f"  min={kmin:+.5f} max={kmax:+.5f} pts={n}")


if __name__ == "__main__":
    calibrate()

    # Degree 2 Cassini: f=z^2-1, roots +-1. Separated regime c<1 -> expect ALL CONVEX.
    analyze("Cassini deg2 z^2-1, c=0.5 (separated)", [1, 0, -1], 0.5, 2.0, "ALL CONVEX")
    analyze("Cassini deg2 z^2-1, c=0.9 (near merge)", [1, 0, -1], 0.9, 2.0, "ALL CONVEX")

    # Goodman (z^2+1)(z-2)^2 = (z^2+1)(z^2-4z+4). Expand:
    # = z^4 -4z^3 +4z^2 + z^2 -4z +4 = z^4 -4z^3 +5z^2 -4z +4
    cgood = 5 ** 1.5 / 4
    for cc in [2.5, 2.7, 2.75, 2.78, cgood, 2.80]:
        analyze(f"Goodman (z^2+1)(z-2)^2, c={cc:.4f}", [1, -4, 5, -4, 4], cc, 4.0, "HAS NON-CONVEX (around z=2)")

    # Referee z(z^5-1)=z^6-z, c=5.6^{-6/5}
    cref = 5.6 ** (-6 / 5)
    analyze(f"Referee z(z^5-1), c={cref:.5f}", [1, 0, 0, 0, 0, -1, 0], cref, 1.5, "HAS NON-CONVEX")

    # Degree 3 all simple roots, symmetric: f=z^3-z=z(z-1)(z+1). Scan c in 3-comp regime.
    print("\n### Degree-3 all-simple-root scan f=z^3-z (probing Goodman 'min degree, simple roots') ###")
    funcs3 = build_g([1, 0, -1, 0])
    for cc in [0.1, 0.2, 0.3, 0.35, 0.38]:
        n = count_components(funcs3, cc, 2.0)
        loops = min_curvature(funcs3, cc, 2.0)
        mk = min((l[0] for l in loops), default=None)
        print(f"  c={cc:.3f} comps={n} min_kappa={mk:+.5f}" if mk is not None else f"  c={cc:.3f} comps={n} (no loops)")
