#!/usr/bin/env python3
"""
birthday-problem-oq-03-oq-01-oq-02-oq-02, Session 4 (researcher-4, 2026-06-15):
CLOSED-FORM absolute three-term expansion of the surrogate triple-collision
threshold, and an independent re-derivation of the second-order coefficient.

Background. S2 (researcher-9) established the *relative* second-order correction
    n*(d) = (6 d^2 ln2)^{1/3} * (1 + (c0/4) d^{-1/3} + ...),  c0 = (6 ln2)^{1/3},
i.e. the d^{1/3} term of n has coefficient c0^2/4, via the first-moment median
solving E[W] = ln2, with W = #{categories receiving >= 3 samples}.

This session pushes one order further IN ABSOLUTE TERMS. Writing the surrogate
root n_W(d) (the real solution of E[W] = ln2, equivalently e^{-E[W]} = 1/2) as
    n_W(d) = c0 d^{2/3} + a d^{1/3} + b + o(1),
we solve the asymptotic expansion of E[W] = d * P(Bin(n, 1/d) >= 3) = ln2 order
by order in t = d^{-1/3}:

  PART A (symbolic, sympy): the t^0, t^1, t^2 coefficients of E[W] give
      t^0:  c0^3/6 = ln2            (defines c0; sanity)
      t^1:  a = c0^2/4              (INDEPENDENT re-derivation of S2's coeff)
      t^2:  b = 1 + 7 c0^3/80 = 1 + (21/40) ln2  ≈ 1.36390227   <-- NEW
  PART B (numeric, mpmath dps=50): high-precision root-finding confirms
      n_W(d) - c0 d^{2/3} - (c0^2/4) d^{1/3}  ->  1 + (21/40) ln2.

RESULT (rigorous for the surrogate n_W):
    n_W(d) = c0 d^{2/3} + (c0^2/4) d^{1/3} + (1 + (21/40) ln2) + o(1).

HONEST CAVEAT. This is exact for the surrogate n_W (a deterministic root). The
TRUE integer median differs by the O(1) Poisson-approximation gap
n*_med - n_W -> ~ -1.03 (S3 Insight 5, numerically estimated, sign = mild
negative day-association). Hence the *constant term* of the integer median is
1 + (21/40)ln2 - 1.03 ~ 0.334 and remains HEURISTIC; only the leading two terms
(c0 d^{2/3} and (c0^2/4) d^{1/3}) and the surrogate constant are rigorous here.

Docker/Aristotle-independent; pure sympy + mpmath.
"""

import sympy as sp
import mpmath as mp

print("=" * 72)
print("PART A: symbolic asymptotic solution of E[W] = ln2")
print("=" * 72)
c0, a, b, t = sp.symbols('c0 a b t', positive=True)
# n = c0/t^2 + a/t + b  with t = d^{-1/3};  p = 1/d = t^3
ns = c0 / t**2 + a / t + b
ps = t**3
logq = sp.log(1 - ps)


def powq(extra):
    # (1 - p)^(ns + extra) = exp((ns+extra) * log(1-p))
    return sp.exp((ns + extra) * logq)


# E[W] = d * [1 - (1-p)^n - n p (1-p)^{n-1} - C(n,2) p^2 (1-p)^{n-2}]
EW = (1 / t**3) * (1 - powq(0) - ns * ps * powq(-1)
                   - ns * (ns - 1) / 2 * ps**2 * powq(-2))
poly = sp.Poly(sp.expand(sp.series(EW, t, 0, 3).removeO()), t)

c_t0 = sp.simplify(poly.coeff_monomial(1))
c_t1 = poly.coeff_monomial(t)
c_t2 = poly.coeff_monomial(t**2)

print("t^0 coefficient of E[W]:", c_t0, "  (must equal ln2 = c0^3/6)")
assert sp.simplify(c_t0 - c0**3 / 6) == 0

a_sol = sp.solve(c_t1, a)[0]
print("t^1 = 0  =>  a =", sp.simplify(a_sol))
assert sp.simplify(a_sol - c0**2 / 4) == 0, "a != c0^2/4"

b_sol = sp.solve(c_t2.subs(a, a_sol), b)[0]
b_sol = sp.simplify(b_sol)
print("t^2 = 0  =>  b =", b_sol)
ln2 = sp.log(2)
b_in_ln2 = sp.simplify(b_sol.subs(c0, (6 * ln2)**sp.Rational(1, 3)))
print("            b =", b_in_ln2, "=", sp.N(b_in_ln2, 15))
assert sp.simplify(b_in_ln2 - (1 + sp.Rational(21, 40) * ln2)) == 0, "b != 1+21ln2/40"
print("PASS: a = c0^2/4 (re-derives S2),  b = 1 + (21/40) ln2.\n")

print("=" * 72)
print("PART B: high-precision numeric confirmation of the constant b")
print("=" * 72)
mp.mp.dps = 50
ln2m = mp.log(2)
c0m = (6 * ln2m)**(mp.mpf(1) / 3)
b_target = 1 + mp.mpf(21) / 40 * ln2m


def EWnum(n, d):
    p = 1 / d
    q = 1 - p
    P0 = q**n
    P1 = n * p * q**(n - 1)
    P2 = n * (n - 1) / 2 * p * p * q**(n - 2)
    return d * (1 - P0 - P1 - P2)


print(f"target b = 1 + (21/40) ln2 = {mp.nstr(b_target, 12)}")
print(" d        n_W - c0 d^(2/3) - (c0^2/4) d^(1/3)")
prev = None
for e in [4, 6, 8, 10, 12, 15, 18]:
    d = mp.mpf(10)**e
    nW = mp.findroot(lambda n: EWnum(n, d) - ln2m, c0m * d**(mp.mpf(2) / 3))
    A = nW - c0m * d**(mp.mpf(2) / 3) - (c0m**2 / 4) * d**(mp.mpf(1) / 3)
    print(f" 1e{e:<2}     {mp.nstr(A, 10)}   (err {mp.nstr(A - b_target, 4)})")
    if prev is not None:
        assert abs(A - b_target) < abs(prev - b_target) + mp.mpf(10)**(-8), "not converging"
    prev = A
assert abs(prev - b_target) < mp.mpf("1e-4"), "did not reach b within 1e-4 by d=1e18"
print("PASS: n_W constant term -> 1 + (21/40) ln2 (monotone convergence).\n")

print("=" * 72)
print("RESULT")
print("=" * 72)
print("n_W(d) = c0 d^(2/3) + (c0^2/4) d^(1/3) + (1 + (21/40) ln2) + o(1),")
print("         c0 = (6 ln2)^(1/3).")
print("Rigorous for the surrogate root n_W. The integer median has an extra")
print("O(1) ~ -1.03 Poisson-gap (S3 Insight 5), so its constant term is heuristic.")
print("\nALL CHECKS PASSED.")
