#!/usr/bin/env python3
"""
birthday-problem-oq-03-oq-01-oq-02-oq-02 -- COMPLETE the symbolic saddle-point
de-Poissonization to extract the next-order gap coefficient g1 as an explicit
closed form (researcher-2, 2026-06-15, S9).

Background (S5/S7/S8):
  gap(d) := n_med(d) - n_W(d) = g_inf + g1 d^{-1/3} + c d^{-2/3} + O(d^{-1}),
    g_inf = -(3/2) ln2 = -c0^3/4   (settled, S5),
    g1    = 0.2322254(1)           (settled NUMERICALLY, S7),
    c0    = (6 ln2)^{1/3}.
  S8 set up the saddle ingredients but PUNTED to numerics; PSLQ over powers of c0
  found no low-height relation for g1.  This script GRINDS the full symbolic series.

Model:  P(no triple) = n! d^{-n} [w^n] f(w)^d,   f(w) = 1 + w + w^2/2.
  n_med solves  -log P(no triple) = ln2.
  n_W   solves  E[W] = ln2,  E[W] = d * P(Bin(n,1/d) >= 3)  (exact binomial).

Saddle point for [w^n] f^d:  G(w) = d log f(w) - (n+1) log w,  G'(rho) = 0
  => n + 1 = d * phi(rho),  phi := w f'/f.
  [w^n] f^d ~ e^{G(rho)} / sqrt(2 pi G''(rho)) * (1 + corr1 + ...),
    corr1 = G4/(8 G2^2) - 5 G3^2/(24 G2^3)   (standard 2nd-order saddle term).

Strategy: express A(rho,d) := -log P(no triple) as an analytic series in rho with
ALL log d cancelling (verified), then solve A = ln2 and E[W] = ln2 as asymptotic
series in D := d^{1/3}; gap = n_med - n_W; read off g_inf, g1, c.
"""
import sympy as sp

w, rho, eps = sp.symbols('w rho epsilon', positive=True)  # eps = 1/d
KMAX = 12  # series order in rho

f  = 1 + w + w**2/2
fp = sp.diff(f, w)
phi = w*fp/f
logf = sp.log(f)

# ---- series (in rho) of the building blocks ----
def ser(expr):
    return sp.series(expr.subs(w, rho), rho, 0, KMAX).removeO()

phi_s   = ser(phi)
logf_s  = ser(logf)
logfp_s = ser(sp.log(fp))
# N(rho) = (log f)'' + phi/rho^2  ; note phi/rho^2 = f'/(rho f) -> 1/rho leading
logf2   = sp.diff(logf, w, 2)
N_expr  = logf2.subs(w, rho) + phi.subs(w, rho)/rho**2
# multiply by rho to clear the 1/rho pole, series, divide back
Nrho_s  = sp.series((rho*N_expr), rho, 0, KMAX).removeO()   # rho*N : analytic, ->1
# G-derivatives /(1/eps): Gk = (1/eps)[ (logf)^{(k)} + c_k phi/rho^{k+1} ],
#   c2=1, c3=-2, c4=6  (from d^k/drho^k of -(n+1)log rho with n+1=d phi)
logf3 = sp.diff(logf, w, 3); logf4 = sp.diff(logf, w, 4)
Gk2 = logf2.subs(w,rho) + phi.subs(w,rho)/rho**2
Gk3 = logf3.subs(w,rho) - 2*phi.subs(w,rho)/rho**3
Gk4 = logf4.subs(w,rho) + 6*phi.subs(w,rho)/rho**4
# corr1 = eps*[ Gk4/(8 Gk2^2) - 5 Gk3^2/(24 Gk2^3) ]   (the 1/eps's collapse to eps)
E1 = Gk4/(8*Gk2**2) - sp.Rational(5,24)*Gk3**2/Gk2**3
E1_s = sp.series(E1, rho, 0, KMAX).removeO()

print("phi(rho)          =", sp.nsimplify(phi_s + sp.O(rho**6)).removeO() if False else phi_s)
print("rho*N(rho)        =", Nrho_s)
print("E1(rho) (corr1/eps)=", sp.series(E1, rho, 0, 4).removeO())

# ---- Build A(rho, eps) = -log P(no triple) -------------------------------
# Derivation (see header). With d=1/eps, n=d*phi-1:
#   A = d*BR(rho) + logQ - 1 - n*log(1-eps/phi) - 1/(12 n) - corr1 + ...
# where
#   BR(rho)   = phi*(log(f/f')+1) - log f               (extensive; * d)
#   logQ      = log( phi * sqrt( N/(phi-eps) ) )         (log d cancels here)
#   corr1     = eps*E1(rho)
# We expand each as a series in rho (and eps), then substitute the asymptotic
# scaling rho ~ c0 d^{-1/3}.
BR = phi*(sp.log(f) - sp.log(fp) + 1) - sp.log(f)
BR_s = ser(BR)            # starts at rho^3
print("\nBR(rho) series    =", BR_s)

# ---- CLEAN LAURENT FORM (avoids 1/phi rational functions) ----------------
# logQ = log(phi) + 1/2 log N - 1/2 log(phi-eps).
#   eps=0 part:        logQ0 = 1/2 log(phi*N)                      (analytic in rho)
#   eps-correction:   -1/2 log(1-eps/phi) = +1/2(u + u^2/2 + u^3/3+...),  u=eps/phi
# Non-extensive ball-count terms expand to (see header derivation):
#   -1 + (-n log(1-u)) = -u/2 - u^2/6 - u^3/12 - ...
#   -1/(12 n)          = -u/12 - u^2/12 - ...
# Sum of ALL eps-corrections collapses:
#   (1/2 u + 1/4 u^2 + 1/6 u^3) + (-u/2 - u^2/6 - u^3/12) + (-u/12 - u^2/12 - ...)
#   = -(1/12) u  + O(u^2 cancels to 0, u^3 cancels to 0)      [verified below]
# So  A = d*BR + 1/2 log(phi*N) - (1/12) eps/phi - eps*E1.
phiN     = (phi*N_expr).subs(w, rho)                   # phi*N : analytic ->1
logQ0_s  = sp.series(sp.Rational(1,2)*sp.log(phiN), rho, 0, KMAX).removeO()
inv_phi  = sp.series((f/(rho*fp)).subs(w, rho), rho, 0, KMAX).removeO()  # 1/phi ~1/rho

# explicit check that the eps-corrections collapse to -(1/12) u :
u = sp.symbols('u', positive=True)
corr_logQ = sp.Rational(1,2)*(u + u**2/2 + u**3/3 + u**4/4)
corr_nlog = -u/2 - u**2/6 - u**3/12 - u**4/20           # from -1 + (-n log(1-u))
corr_inv  = -(u/12 + u**2/12 + u**3/12 + u**4/12)        # from -1/(12n)
collapse  = sp.expand(corr_logQ + corr_nlog + corr_inv)
print("\neps-correction collapse (should be -(1/12)u + O(u^2)):", sp.series(collapse,u,0,4).removeO())

A = (BR_s/eps                                  # d*BR
     + logQ0_s                                 # 1/2 log(phi*N)
     - sp.Rational(1,12)*eps*inv_phi           # -(1/12) eps/phi
     - eps*E1_s)                               # -corr1
A = sp.expand(A)
print("A assembled (clean Laurent). #terms:", len(A.args) if A.is_Add else 1)

# The asymptotic solve A=ln2 (-> g_inf, g1) lives in the sibling driver
# verify_birthday_oq03_g1_solve.py, which imports A, phi_s, rho, eps from here.
if __name__ == '__main__':
    print("\nThis module defines the symbolic exponent A; run the driver "
          "verify_birthday_oq03_g1_solve.py for the g1 extraction.")
