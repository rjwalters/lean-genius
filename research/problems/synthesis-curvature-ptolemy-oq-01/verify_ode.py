#!/usr/bin/env python3
"""
Durable EXACT (symbolic) verification for synthesis-curvature-ptolemy-oq-01.

Claim (OQ-01): the curvature-parametrized function

    curvatureSin K t =
        | t                         (K = 0,  Euclidean)
        | sin(sqrt(K)  * t)/sqrt(K)   (K > 0,  spherical)
        | sinh(sqrt(-K)* t)/sqrt(-K)  (K < 0,  hyperbolic)

satisfies the second-order linear ODE

    y'' + K * y = 0

for all K and t, with initial conditions y(0)=0, y'(0)=1.

This script confirms, by exact symbolic differentiation (no floating point):
  1. the first-derivative closed form ("curvatureCos"),
  2. the ODE  y'' + K*y == 0,
  3. the initial conditions y(0)=0, y'(0)=1,
in each of the three curvature regimes.

These are exactly the statements formalized in
proofs/Proofs/SynthesisCurvaturePtolemyOQ01.lean
(curvatureSin_hasDerivAt, curvatureCos_hasDerivAt, curvatureSin_satisfies_ode,
curvatureSin_initial_conditions).
"""
import sympy as sp

t = sp.symbols('t', real=True)

cases = []

# K > 0 (spherical): K = Kp > 0
Kp = sp.symbols('Kp', positive=True)
cases.append(("K>0  (spherical)",
              sp.sin(sp.sqrt(Kp) * t) / sp.sqrt(Kp),  # y
              Kp,                                       # K value
              sp.cos(sp.sqrt(Kp) * t)))                # expected curvatureCos

# K = 0 (Euclidean)
cases.append(("K=0  (Euclidean)",
              t,
              sp.Integer(0),
              sp.Integer(1)))

# K < 0 (hyperbolic): K = -m, m > 0
m = sp.symbols('m', positive=True)
cases.append(("K<0  (hyperbolic)",
              sp.sinh(sp.sqrt(m) * t) / sp.sqrt(m),
              -m,
              sp.cosh(sp.sqrt(m) * t)))

all_ok = True
for name, y, K, expected_cos in cases:
    yp = sp.simplify(sp.diff(y, t))
    ypp = sp.diff(y, t, 2)
    ode = sp.simplify(ypp + K * y)
    cos_ok = sp.simplify(yp - expected_cos) == 0
    ode_ok = (ode == 0)
    y0 = sp.simplify(y.subs(t, 0))
    yp0 = sp.simplify(yp.subs(t, 0))
    ic_ok = (y0 == 0) and (yp0 == 1)
    ok = cos_ok and ode_ok and ic_ok
    all_ok = all_ok and ok
    print(f"[{ 'PASS' if ok else 'FAIL'}] {name}")
    print(f"        y'            = {yp}        (curvatureCos match: {cos_ok})")
    print(f"        y'' + K*y     = {ode}        (ODE holds: {ode_ok})")
    print(f"        y(0), y'(0)   = {y0}, {yp0}  (initial conditions: {ic_ok})")

print()
print("ALL EXACT CHECKS PASS" if all_ok else "SOME CHECK FAILED")
import sys
sys.exit(0 if all_ok else 1)
