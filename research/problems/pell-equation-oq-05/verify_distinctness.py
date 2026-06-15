#!/usr/bin/env python3
"""
pell-equation-oq-05, Session 5 (ACT): distinctness / infinitude certificate.

S4 (PR #24277) formalized the cubic norm form N(a,b,c)=a^3+2b^3+4c^3-6abc of
K=Q(cbrt 2)=Z[t]/(t^3-2), its multiplicativity, the fundamental unit u=t-1 of
norm 1, and the Pell chain u^k (all of norm 1). But S4 explicitly LEFT OPEN the
claim "infinitely many solutions of N(xi)=1": it never proved the chain values
u^k are DISTINCT.

This script verifies, symbolically and from first principles, the S5 argument
that closes that gap WITHOUT any signature/Dirichlet machinery:

  (A) phi(p)=p0 + p1*tau + p2*tau^2 (tau=real cube root of 2) is a ring hom:
      phi(cmul x y) = phi(x)*phi(y), the polynomial identity using tau^3=2.
  (B) 1 < tau < 2, hence phi(u) = tau-1 in (0,1).
  (C) phi(u^k) = phi(u)^k is strictly decreasing in k (base in (0,1)),
      hence the u^k are pairwise distinct.
  (D) => {p : N(p)=1} is infinite (injective chain inside the norm-1 set).

Everything is checked with exact sympy arithmetic (no floats in the proofs;
floats only for a human-readable sanity print). Docker/Aristotle-independent.
"""

import sympy as sp

a0, a1, a2, b0, b1, b2, tau = sp.symbols('a0 a1 a2 b0 b1 b2 tau')


def cnorm(a, b, c):
    return a**3 + 2*b**3 + 4*c**3 - 6*a*b*c


def cmul(x, y):
    x0, x1, x2 = x
    y0, y1, y2 = y
    return (x0*y0 + 2*(x1*y2 + x2*y1),
            x0*y1 + x1*y0 + 2*x2*y2,
            x0*y2 + x1*y1 + x2*y0)


def cnorm3(p):
    return cnorm(p[0], p[1], p[2])


def phi(p):
    # real embedding t -> tau, tau^3 = 2
    return p[0] + p[1]*tau + p[2]*tau**2


def reduce_tau(expr):
    """Reduce a polynomial in tau modulo tau^3 - 2 (i.e. set tau^3 = 2)."""
    poly = sp.Poly(sp.expand(expr), tau)
    # rem of poly by (tau^3 - 2)
    _, rem = sp.div(poly, sp.Poly(tau**3 - 2, tau), tau)
    return sp.expand(rem.as_expr())


print("=" * 70)
print("(A) phi is a ring homomorphism:  phi(cmul x y) == phi(x)*phi(y) mod tau^3-2")
print("=" * 70)
x = (a0, a1, a2)
y = (b0, b1, b2)
lhs = reduce_tau(phi(cmul(x, y)))
rhs = reduce_tau(phi(x) * phi(y))
diff = sp.expand(lhs - rhs)
print("phi(cmul x y) - phi(x)*phi(y)  (mod tau^3-2)  =", diff)
assert diff == 0, "phi is NOT a ring hom!"
print("PASS: phi respects multiplication.\n")

# explicit linear_combination coefficient for the Lean proof:
# phi(x)*phi(y) - phi(cmul x y) = (tau^3 - 2) * C, find C
full = sp.expand(phi(x)*phi(y) - phi(cmul(x, y)))
C = sp.simplify(sp.cancel(full / (tau**3 - 2)))
print("Lean linear_combination coefficient C with")
print("  phi(x)*phi(y) - phi(cmul x y) = (tau^3 - 2) * C :")
print("  C =", sp.expand(C))
assert sp.expand(full - (tau**3 - 2)*C) == 0
print("  (verified exact)\n")

print("=" * 70)
print("(B) tau in (1,2)  =>  phi(u) = tau - 1 in (0,1)")
print("=" * 70)
tau_val = sp.Rational(2)**sp.Rational(1, 3)
print("tau = 2^(1/3) ~", float(tau_val))
assert tau_val**3 == 2
assert 1 < tau_val < 2
u = (-1, 1, 0)
phi_u = phi(u).subs(tau, tau_val)
print("phi(u) = tau - 1 ~", float(phi_u))
assert 0 < phi_u < 1
print("PASS: 0 < phi(u) < 1.\n")

print("=" * 70)
print("(C) phi(u^k) = phi(u)^k strictly decreasing => u^k pairwise distinct")
print("=" * 70)


def upow(k):
    p = (1, 0, 0)
    for _ in range(k):
        p = cmul(p, u)
    return p


prev = None
seen = {}
for k in range(0, 12):
    p = upow(k)
    # check norm 1
    assert cnorm3(p) == 1, f"N(u^{k}) != 1"
    # check phi(u^k) = phi(u)^k exactly
    val_chain = phi(p).subs(tau, tau_val)
    val_pow = phi_u**k
    assert sp.simplify(val_chain - val_pow) == 0, f"phi(u^{k}) != phi(u)^{k}"
    # strictly decreasing
    if prev is not None:
        assert val_chain < prev, "phi(u^k) not strictly decreasing"
    prev = val_chain
    # distinctness of the triples themselves
    assert p not in seen, f"collision: u^{k} == u^{seen.get(p)}"
    seen[p] = k
    print(f"u^{k:2d} = {str(p):>16s}   N=1   phi=phi(u)^{k} ~ {float(val_chain):.6e}")
print("PASS: all 12 chain values distinct, norms 1, phi(u^k)=phi(u)^k decreasing.\n")

print("=" * 70)
print("(D) {p : N(p)=1} is infinite")
print("=" * 70)
print("k |-> u^k is injective (C) and lands in {N=1} (S4 cnorm_upow),")
print("so the norm-one solution set contains an infinite subset => infinite.")
print("PASS (structural).\n")

print("=" * 70)
print("(E) Session 6: N(xi)=m has 0 or infinitely many solutions")
print("=" * 70)
print("Norm-form factorization at the real place (cubic analogue of")
print("x^3+y^3+z^3-3xyz=(x+y+z)(x^2+y^2+z^2-xy-yz-zx) with (x,y,z)=(a,b*tau,c*tau^2)):")
A, B, C, t = sp.symbols('A B C t')
cn = cnorm(A, B, C)
phi_p = A + B * t + C * t**2
# the conjugate-product factor xi_star = (A^2-2BC, 2C^2-AB, B^2-AC)
phi_star = (A**2 - 2 * B * C) + (2 * C**2 - A * B) * t + (B**2 - A * C) * t**2
# reduce phi_p * phi_star modulo t^3 - 2 and compare to cnorm
_, rem = sp.div(sp.Poly(sp.expand(phi_p * phi_star), t), sp.Poly(t**3 - 2, t))
assert sp.expand(rem.as_expr() - cn) == 0, "factorization N=phi*phi_star failed"
print("  N(a,b,c) = phi(a,b,c) * phi(a^2-2bc, 2c^2-ab, b^2-ac)  (mod t^3-2)  OK")
# linear_combination coefficient used in the Lean proof (cnorm_eq_phi_mul)
e = 2 * A * B * C + A * C**2 * t - B**3 - B**2 * C * t - 2 * C**3
assert sp.expand((cn - phi_p * phi_star) - e * (t**3 - 2)) == 0, "lin_comb coeff wrong"
print("  linear_combination coefficient (cnorm - phi*phi_star = e*(t^3-2))  OK")
print("Consequence: N(p) != 0 => phi(p) != 0, so for any solvable N(xi)=m (m!=0)")
print("the shifted chain k |-> xi0 * u^k is injective (phi(xi0)*phi(u)^k) and lands")
print("in {N=m}; hence {p : N(p)=m} is infinite. Instance: N(cbrt2)=2 => N=2 infinite.")
assert cnorm(0, 1, 0) == 2, "N(cbrt2) != 2"
print("  N(0,1,0) = 2  OK\n")

print("ALL CHECKS PASSED.")
