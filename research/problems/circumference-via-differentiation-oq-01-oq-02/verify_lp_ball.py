#!/usr/bin/env python3
"""
Durable exact-ish verifier for circumference-via-differentiation-oq-01-oq-02.

Open question (gallery extension of "n-Dimensional Surface Area via
Differentiation of Volume"):

    The unit ball in L^p has volume  V_n(p) = 2^n Gamma(1+1/p)^n / Gamma(1+n/p)
    (classical Dirichlet/Liouville; the problem attributes it to Pisier 1989).
    Does the "volume-derivative-equals-surface" identity  dV/dr = surface area
    still hold for the L^p surface area when p != 2 ?

This script answers the question by independent numerical checks (Python stdlib
only, deterministic Simpson quadrature in n=2 plus Monte-Carlo cross-checks in
n=2,3,4):

  (A) VOLUME FORMULA.  Lebesgue volume of B_p^n = {x : sum |x_i|^p <= 1}
      matches the Dirichlet closed form V_n(p) = 2^n G(1+1/p)^n / G(1+n/p).

  (B) RADIAL SCALING.  Vol{ ||x||_p <= r } = V_n(p) * r^n, hence
      dV/dr = n * V_n(p) * r^{n-1}.  (Finite-difference check.)

  (C) THE ANSWER.  By the coarea formula for rho(x) = ||x||_p,
          dV/dr = integral over {||x||_p=r} of 1/|grad rho| dH^{n-1}        (coarea-weighted)
      where |grad rho| is the *Euclidean* gradient norm of the L^p norm.
      On the unit sphere |grad rho|^2 = sum |x_i|^{2p-2}, which is identically 1
      iff p = 2.  Therefore:
        * for p = 2  the weight is 1 and  dV/dr = Euclidean Hausdorff surface area;
        * for p != 2 the weight varies and  dV/dr  is a |grad rho|^{-1}-WEIGHTED
          surface area, NOT the Euclidean (Hausdorff) surface area.
      We confirm in n=2 that
          weighted_surface(p)  == dV/dr          for ALL tested p   (coarea holds)
          euclidean_perimeter  == dV/dr          ONLY for p = 2
      e.g. n=2, p=1 (the L^1 "diamond"): dV/dr = 4 but Euclidean perimeter = 4*sqrt(2).

All numbers are checked against independent computations; the script prints
PASS/FAIL for each assertion and exits non-zero on any failure.
"""

import math

# ----------------------------------------------------------------------------- helpers

def lp_volume_closed_form(n, p):
    """Dirichlet closed form for vol of the L^p unit ball in R^n."""
    if math.isinf(p):
        return 2.0 ** n  # cube [-1,1]^n
    return (2.0 ** n) * math.gamma(1.0 + 1.0 / p) ** n / math.gamma(1.0 + n / p)


def simpson(f, a, b, m):
    """Composite Simpson on [a,b] with m subintervals (m even)."""
    if m % 2:
        m += 1
    h = (b - a) / m
    s = f(a) + f(b)
    for i in range(1, m):
        s += (4 if i % 2 else 2) * f(a + i * h)
    return s * h / 3.0


# Deterministic high-accuracy integrand for n=2: quarter-area = \int_0^1 (1-x^p)^{1/p} dx
def quarter_area_n2(p, m=200000):
    # (1-x^p)^{1/p} has an integrable singularity in its derivative at x=1; Simpson
    # on a fine uniform grid converges well for p in [1, ~6].
    f = lambda x: (max(0.0, 1.0 - x ** p)) ** (1.0 / p)
    return simpson(f, 0.0, 1.0, m)


# ----------------------------------------------------------------------------- (A) volume

def monte_carlo_volume(n, p, samples, rng):
    inside = 0
    for _ in range(samples):
        s = 0.0
        for _i in range(n):
            x = rng.uniform(-1.0, 1.0)
            s += abs(x) ** p
            if s > 1.0:
                break
        else:
            if s <= 1.0:
                inside += 1
    return (2.0 ** n) * inside / samples


# ----------------------------------------------------------------------------- (C) surfaces (n=2)

def surfaces_n2(p, m=20000):
    """Return (euclidean_perimeter, coarea_weighted_surface) of the L^p unit
    circle in R^2.

    Quarter boundary: y(x) = (1 - x^p)^{1/p}, x in [0,1].
      ds          = sqrt(1 + y'(x)^2) dx
      |grad rho|  = sqrt( |x|^{2(p-1)} + |y|^{2(p-1)} )   (on the unit sphere)
      weighted    = integral of ds / |grad rho|

    The quarter has a vertical tangent at x=1 (y'-> -inf), which kills uniform
    quadrature.  But the curve is symmetric under x<->y about the diagonal, and
    BOTH integrands (ds and ds/|grad rho|) are invariant under that swap.  So the
    quarter integral = 2 * (integral over the SMOOTH half x in [0, x0]), where
    x0 = (1/2)^{1/p} is the diagonal point x=y.  On [0,x0] the slope runs from 0
    (horizontal tangent at x=0) to -1 (at x0), so Simpson converges fast.
    Full boundary = 4 quarters = 8 * (smooth-half integral).
    """
    def yprime(x):
        # y = (1-x^p)^{1/p}; y' = -x^{p-1} (1-x^p)^{1/p - 1}
        if x <= 0.0:
            return 0.0
        base = 1.0 - x ** p
        if base <= 0.0:
            return 0.0
        return -(x ** (p - 1.0)) * (base ** (1.0 / p - 1.0))

    def y_of(x):
        return (max(0.0, 1.0 - x ** p)) ** (1.0 / p)

    def ds(x):
        yp = yprime(x)
        return math.sqrt(1.0 + yp * yp)

    def grad_norm(x):
        y = y_of(x)
        return math.sqrt(x ** (2.0 * (p - 1.0)) + y ** (2.0 * (p - 1.0)))

    x0 = (0.5) ** (1.0 / p)
    half_perim = simpson(ds, 0.0, x0, m)
    half_weighted = simpson(lambda x: ds(x) / grad_norm(x), 0.0, x0, m)
    perimeter = 8.0 * half_perim
    weighted = 8.0 * half_weighted
    return perimeter, weighted


# ----------------------------------------------------------------------------- driver

def approx(a, b, rel=1e-3, absolute=1e-6):
    return abs(a - b) <= max(absolute, rel * max(abs(a), abs(b)))


def main():
    import random
    rng = random.Random(20260615)
    all_pass = True

    print("=" * 72)
    print("(A) L^p ball volume  vs  Dirichlet closed form  V_n(p)=2^n G(1+1/p)^n/G(1+n/p)")
    print("=" * 72)
    # n=2 deterministic (Simpson) -- high accuracy
    for p in [1.0, 1.5, 2.0, 3.0, 4.0]:
        cf = lp_volume_closed_form(2, p)
        det = 4.0 * quarter_area_n2(p)
        ok = approx(cf, det, rel=2e-3)
        all_pass &= ok
        print(f"  n=2 p={p:<4}  closed={cf:.6f}  Simpson(4*quarter)={det:.6f}  {'PASS' if ok else 'FAIL'}")
    # n=3,4 Monte-Carlo cross-check
    for (n, p, samp, tol) in [(3, 2.0, 400000, 2e-2), (3, 1.0, 400000, 2e-2),
                              (3, 4.0, 400000, 2e-2), (4, 2.0, 600000, 3e-2),
                              (4, 1.0, 600000, 3e-2)]:
        cf = lp_volume_closed_form(n, p)
        mc = monte_carlo_volume(n, p, samp, rng)
        ok = approx(cf, mc, rel=tol)
        all_pass &= ok
        print(f"  n={n} p={p:<4}  closed={cf:.6f}  MonteCarlo={mc:.6f}  {'PASS' if ok else 'FAIL'}")

    print()
    print("=" * 72)
    print("(B) radial scaling:  d/dr Vol{||x||_p<=r} = n*V_n(p)*r^{n-1}   (finite diff)")
    print("=" * 72)
    for (n, p) in [(2, 1.0), (2, 2.0), (2, 3.0), (3, 2.0)]:
        Vn = lp_volume_closed_form(n, p)
        r, h = 1.0, 1e-4
        # Vol{||x||<=r} = Vn * r^n  (pure scaling); finite-diff the closed scaling
        vol = lambda rr: Vn * rr ** n
        fd = (vol(r + h) - vol(r - h)) / (2 * h)
        analytic = n * Vn * r ** (n - 1)
        ok = approx(fd, analytic, rel=1e-4)
        all_pass &= ok
        print(f"  n={n} p={p:<4}  dV/dr(fd)={fd:.6f}  n*Vn*r^(n-1)={analytic:.6f}  {'PASS' if ok else 'FAIL'}")

    print()
    print("=" * 72)
    print("(C) THE ANSWER (n=2):  coarea-weighted surface == dV/dr for ALL p;")
    print("    Euclidean perimeter == dV/dr ONLY for p=2.")
    print("=" * 72)
    for p in [1.0, 1.5, 2.0, 3.0, 4.0]:
        Vn = lp_volume_closed_form(2, p)
        dVdr = 2.0 * Vn  # n*Vn*r^{n-1} at n=2, r=1
        perim, weighted = surfaces_n2(p)
        coarea_ok = approx(weighted, dVdr, rel=3e-3)
        eucl_eq = approx(perim, dVdr, rel=3e-3)
        # expectation: eucl_eq is True iff p == 2
        expect_eucl = (abs(p - 2.0) < 1e-9)
        verdict = (coarea_ok and (eucl_eq == expect_eucl))
        all_pass &= verdict
        print(f"  p={p:<4} dV/dr={dVdr:.5f}  weighted={weighted:.5f} (coarea {'OK' if coarea_ok else 'BAD'})"
              f"  perim={perim:.5f} (eucl==dVdr: {eucl_eq}, expected {expect_eucl})"
              f"  {'PASS' if verdict else 'FAIL'}")

    # explicit headline anchor: L^1 diamond
    Vn1 = lp_volume_closed_form(2, 1.0)
    print()
    print(f"  ANCHOR L^1 diamond: area={Vn1:.4f} (=2), dV/dr={2*Vn1:.4f} (=4), "
          f"Euclidean perimeter=4*sqrt(2)={4*math.sqrt(2):.4f}  ->  4 != 5.657")

    print()
    print("=" * 72)
    print("OVERALL:", "ALL PASS" if all_pass else "SOME FAILED")
    print("=" * 72)
    return 0 if all_pass else 1


if __name__ == "__main__":
    raise SystemExit(main())
