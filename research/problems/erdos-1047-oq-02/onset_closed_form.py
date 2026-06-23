#!/usr/bin/env python3
"""
Closed-form non-convexity onset for the Pommerenke family f = z^k (z-1).

Builds on the Session-2 closed-form curvature criterion (knowledge.md):

    a component of {|f| <= c} is convex  <=>  Re( f f'' / (f')^2 ) <= 1
                                                          =: Re Phi(z) <= 1

on its boundary. The non-convex region N = {Re Phi > 1} is FIXED in the plane
while {|f| = c} grows with c, so the component around the root at 0 first becomes
non-convex at

    c_nc = min |f(z)|  over the zero-curvature locus  {Re Phi(z) = 1},

a constrained minimum with NO scan in c. The Lagrange condition for
min |f|^2 s.t. Re Phi = 0-level is

    Im( f'(z) * conj(f(z)) * conj(Phi'(z)) ) = 0        (gradients parallel)
    Re Phi(z) = 1.

For f = z^2 (z-1) one finds the remarkably clean derivative

    Phi(z) = 2 (z-1)(3z-1) / (3z-2)^2 ,     Phi'(z) = 4 / (3z-2)^3 ,

and the Lagrange system has an off-axis solution z = x + i y giving the
CLOSED FORM (recognized by PSLQ at 70+ digits, residuals ~1e-60):

    x   = (40 - sqrt 10) / 60
    y^2 = (13 - 4 sqrt 10) / 120
    c_nc(2,1)^2 = (130 - 31 sqrt 10) / 1458         [1458 t^2 - 260 t + 5 = 0]
    c_nc(2,1)   = sqrt( (130 - 31 sqrt 10) / 1458 ) = 0.148077280584...

(Compare the merge threshold c* = |f(2/3)| = 4/27 = 0.148148...; the non-convex
window W = (c* - c_nc)/c* = 0.000478, matching the prior bisection table.)

The same method gives, for higher multiplicity (c_nc^2 algebraic, degree rising):
    (3,1):  26214400 t^2 - 3522960 t + 35721 = 0     (t = c_nc^2; degree 2)
    (5,1):  a degree-4 minimal polynomial in t        (c_nc degree 8)

So the onset is an algebraic number whose degree grows with the root
multiplicity; (2,1) is the cleanest (a quadratic in sqrt 10).

Reproducible, Docker-independent. Requires mpmath, numpy.
"""
import mpmath as mp
import numpy as np

mp.mp.dps = 70


def family(k):
    def f(z):   return z ** k * (z - 1)
    def fp(z):  return z ** (k - 1) * ((k + 1) * z - k)
    def fpp(z): return (k - 1) * z ** (k - 2) * ((k + 1) * z - k) + z ** (k - 1) * (k + 1)
    def Phi(z): return f(z) * fpp(z) / fp(z) ** 2
    return f, fp, Phi


def seed(k):
    """numpy grid scan of the zero-curvature locus to seed the high-prec solve."""
    f, fp, Phi = family(k)
    fn = lambda z: z ** k * (z - 1)
    saddle = k / (k + 1)
    cstar = abs(fn(saddle))
    xs = np.linspace(-0.9, saddle * 0.999, 1600)
    ys = np.linspace(0.005, 0.9, 1600)
    X, Y = np.meshgrid(xs, ys)
    Z = X + 1j * Y
    with np.errstate(all="ignore"):
        fpp = (k - 1) * Z ** (k - 2) * ((k + 1) * Z - k) + Z ** (k - 1) * (k + 1)
        R = np.real(fn(Z) * fpp / (Z ** (k - 1) * ((k + 1) * Z - k)) ** 2)
        A = np.abs(fn(Z))
    m = np.isfinite(R) & (np.abs(R - 1) < 0.02) & np.isfinite(A) & (A < cstar * 1.02)
    am = A[m]
    i = int(np.argmin(am))
    return cstar, float(X[m][i]), float(Y[m][i])


def onset(k):
    f, fp, Phi = family(k)
    cstar, x0, y0 = seed(k)

    def eqs(a, b):
        z = mp.mpc(a, b)
        php = mp.diff(Phi, z)
        return [mp.re(Phi(z)) - 1, mp.im(fp(z) * mp.conj(f(z)) * mp.conj(php))]

    s = mp.findroot(eqs, (mp.mpf(repr(x0)), mp.mpf(repr(y0))), tol=mp.mpf(10) ** -40)
    x, y = s[0], s[1]
    z = mp.mpc(x, y)
    c = abs(f(z))
    return cstar, c, x, y


def minpoly(val, maxdeg=8):
    for d in range(2, maxdeg + 1):
        rel = mp.pslq([val ** j for j in range(d + 1)], maxcoeff=10 ** 13, maxsteps=10 ** 6)
        if rel and any(rel):
            return d, rel
    return None, None


def main():
    ok = True
    # (2,1) closed form check
    r10 = mp.sqrt(10)
    cstar, c, x, y = onset(2)
    cnc2_cf = (130 - 31 * r10) / 1458
    x_cf = (40 - r10) / 60
    y2_cf = (13 - 4 * r10) / 120
    print("=== (2,1): f = z^2 (z-1) ===")
    print("  c* (= 4/27)        =", mp.nstr(cstar, 20))
    print("  c_nc numeric       =", mp.nstr(c, 30))
    print("  c_nc closed form   =", mp.nstr(mp.sqrt(cnc2_cf), 30))
    for nm, num, cf in [("c_nc^2", c * c, cnc2_cf), ("x", x, x_cf), ("y^2", y * y, y2_cf)]:
        d = abs(num - cf)
        print(f"  {nm:7s} |numeric - closed| = {mp.nstr(d, 3)}")
        ok &= d < mp.mpf(10) ** -30
    # (3,1), (5,1) minimal polynomials
    for k in (3, 5):
        cstar, c, x, y = onset(k)
        d, rel = minpoly(c * c)
        print(f"=== ({k},1) ===  c_nc^2={mp.nstr(c*c,24)}  "
              f"W={mp.nstr((cstar-c)/cstar,6)}  minpoly(c_nc^2) deg={d}")
        print(f"           rel(c_nc^2) = {rel}")
        ok &= d is not None
    print("RESULT:", "PASS" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
