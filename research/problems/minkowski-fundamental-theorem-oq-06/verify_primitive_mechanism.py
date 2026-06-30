#!/usr/bin/env python3
"""
Durable verification for minkowski-fundamental-theorem-oq-06 (Minkowski-Hlawka):
WHERE the factor zeta(n) in delta_n >= zeta(n)/2^(n-1) actually comes from.

Companion to verify_minkowski_hlawka.py. That script pins the *constants* and the
statement<->density chain. This script isolates the *mechanism*: the zeta(n) factor
is the PRIMITIVE-vector (Siegel-Rogers) restriction, a distinct and deeper input
than the elementary +/- pairing (which only contributes the factor 2).

Background (the staged-formalization hypothesis, sharpened):
  Siegel's mean-value theorem (all nonzero vectors):
      INT_{X_n} sum_{v in L\\{0}} f(v) dmu(L) = INT_{R^n} f(x) dx,        (S)
  where X_n = SL_n(Z)\\SL_n(R) with its PROBABILITY Haar measure mu.
  Decompose each nonzero v uniquely as v = m * w, m >= 1, w primitive. Scaling
  f(m * .) integrates to m^{-n} INT f, so if the PRIMITIVE-vector mean is c * INT f,
  then (S) reads  c * INT f * sum_{m>=1} m^{-n} = INT f, i.e.
      c = 1 / sum_{m>=1} m^{-n} = 1 / zeta(n).                           (R)
  Hence the Siegel-Rogers PRIMITIVE mean-value formula:
      INT_{X_n} sum_{w in L primitive} f(w) dmu(L) = (1/zeta(n)) INT_{R^n} f.

Minkowski-Hlawka via (R): for symmetric S (0 notin S), primitive vectors in S come
in +/- pairs, so the mean number of primitive +/- PAIRS in S is vol(S)/(2 zeta(n)).
If vol(S) < 2 zeta(n) the mean is < 1, so some unimodular L has NO primitive vector
in S. For the ball case the shortest nonzero vector is always primitive, so "no
primitive vector in ball(2r)" => min distance >= 2r => packing density >= zeta(n)/2^(n-1).

  => The 2 is the +/- pairing.  The zeta(n) is the primitivity restriction (R).
     These are independent; conflating them mis-states the staged hypothesis.

What is checked here:
  (1) The decomposition identity zeta(n) = sum_{m>=1} m^{-n}, so c = 1/zeta(n).
  (2) For Z^2 the fraction of nonzero lattice points that are primitive (= visible
      from the origin, gcd(x,y)=1) converges to 1/zeta(2) = 6/pi^2: a concrete,
      lattice-level witness that the primitivity restriction carries exactly the
      zeta factor.
  (3) For Z^3 the primitive fraction converges to 1/zeta(3).
  (4) The shortest nonzero vector of an integer lattice is always primitive
      (justifies that primitive-only counting suffices for the ball/packing case).

Run:  python3 verify_primitive_mechanism.py
Requires: only the standard library (math). sympy used if present for exact zeta.
"""

import math
from math import gcd, pi

try:
    from sympy import zeta as sym_zeta
    HAVE_SYMPY = True
except Exception:
    HAVE_SYMPY = False


def zeta_f(n: int, terms: int = 400000) -> float:
    if HAVE_SYMPY:
        return float(sym_zeta(n))
    return sum(m ** (-n) for m in range(1, terms))


def check_decomposition_identity() -> bool:
    """(1) zeta(n) = sum_{m>=1} m^{-n}; the primitive-mean coeff is 1/zeta(n)."""
    ok = True
    print("[1] decomposition  zeta(n) = sum_{m>=1} m^{-n}  =>  c = 1/zeta(n)")
    for n in (2, 3, 4, 8):
        partial = sum(m ** (-n) for m in range(1, 400000))
        z = zeta_f(n)
        err = abs(partial - z)
        good = err < 1e-4
        ok &= good
        print(f"    n={n}: sum_m m^-n={partial:.6f}  zeta(n)={z:.6f}  "
              f"1/zeta={1/z:.6f}  err={err:.2e}  {'OK' if good else 'FAIL'}")
    # exact anchor for n=2
    anchor = abs(zeta_f(2) - pi * pi / 6) < 1e-9
    ok &= anchor
    print(f"    anchor zeta(2)=pi^2/6: {'OK' if anchor else 'FAIL'}")
    return ok


def primitive_fraction_Zn(dim: int, R: int) -> float:
    """Fraction of nonzero points of Z^dim in [-R,R]^dim that are primitive."""
    total = 0
    prim = 0
    if dim == 2:
        for x in range(-R, R + 1):
            for y in range(-R, R + 1):
                if x == 0 and y == 0:
                    continue
                total += 1
                if gcd(abs(x), abs(y)) == 1:
                    prim += 1
    elif dim == 3:
        for x in range(-R, R + 1):
            for y in range(-R, R + 1):
                for z in range(-R, R + 1):
                    if x == 0 and y == 0 and z == 0:
                        continue
                    total += 1
                    if gcd(gcd(abs(x), abs(y)), abs(z)) == 1:
                        prim += 1
    else:
        raise ValueError("dim in {2,3}")
    return prim / total


def check_primitive_fraction_Z2() -> bool:
    """(2) Z^2 primitive fraction -> 1/zeta(2) = 6/pi^2."""
    target = 6 / pi ** 2
    print(f"[2] Z^2 primitive fraction -> 1/zeta(2) = 6/pi^2 = {target:.6f}")
    ok = True
    last = None
    for Rb in (50, 150, 400):
        f = primitive_fraction_Zn(2, Rb)
        err = abs(f - target)
        good = err < 0.01
        ok &= good
        last = f
        print(f"    R={Rb}: fraction={f:.6f}  err={err:.5f}  {'OK' if good else 'FAIL'}")
    return ok and last is not None


def check_primitive_fraction_Z3() -> bool:
    """(3) Z^3 primitive fraction -> 1/zeta(3)."""
    target = 1 / zeta_f(3)
    print(f"[3] Z^3 primitive fraction -> 1/zeta(3) = {target:.6f}")
    ok = True
    for Rb in (20, 40, 70):
        f = primitive_fraction_Zn(3, Rb)
        err = abs(f - target)
        good = err < 0.01
        ok &= good
        print(f"    R={Rb}: fraction={f:.6f}  err={err:.5f}  {'OK' if good else 'FAIL'}")
    return ok


def check_shortest_is_primitive() -> bool:
    """(4) shortest nonzero lattice vector is always primitive (deterministic sweep)."""
    print("[4] shortest nonzero vector is primitive (=> primitive-only suffices for balls)")
    ok = True
    tot = 0
    good = 0
    # deterministic sweep over a grid of integer 2x2 bases (no RNG, reproducible)
    rng = range(-5, 6)
    for a0 in rng:
        for a1 in rng:
            for b0 in rng:
                for b1 in rng:
                    det = a0 * b1 - a1 * b0
                    if det == 0:
                        continue
                    tot += 1
                    best = None
                    bestnorm = None
                    for i in range(-6, 7):
                        for j in range(-6, 7):
                            if i == 0 and j == 0:
                                continue
                            vx = a0 * i + b0 * j
                            vy = a1 * i + b1 * j
                            nrm = vx * vx + vy * vy
                            if bestnorm is None or nrm < bestnorm:
                                bestnorm = nrm
                                best = (i, j)
                    if gcd(abs(best[0]), abs(best[1])) == 1:
                        good += 1
    ok = (good == tot) and tot > 0
    print(f"    primitive-shortest: {good}/{tot}  {'OK' if ok else 'FAIL'}")
    return ok


def main() -> int:
    print("=" * 70)
    print("Minkowski-Hlawka: the zeta(n) factor is PRIMITIVITY, not +/- pairing")
    print("=" * 70)
    results = [
        ("decomposition zeta=sum m^-n", check_decomposition_identity()),
        ("Z^2 primitive fraction", check_primitive_fraction_Z2()),
        ("Z^3 primitive fraction", check_primitive_fraction_Z3()),
        ("shortest vector primitive", check_shortest_is_primitive()),
    ]
    print("-" * 70)
    all_ok = all(r for _, r in results)
    for name, r in results:
        print(f"  {'PASS' if r else 'FAIL'}  {name}")
    print("-" * 70)
    print("ALL CHECKS PASS" if all_ok else "SOME CHECKS FAILED")
    return 0 if all_ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
