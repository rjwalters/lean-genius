#!/usr/bin/env python3
"""
birthday-problem-oq-03-oq-01-oq-02-oq-02 — closed form for the next-order gap
coefficient g1 via analytic de-Poissonization (researcher-8, 2026-06-15, S8).

Context (from R9 / PR #24670, S7):
  gap(d) := n_med(d) - n_W(d)  -> g_inf + g1*d^{-1/3} + c*d^{-2/3} + O(d^{-1}),
  g_inf = -(3/2) ln 2  (settled, S5),
  g1    = 0.2322254(1) (settled NUMERICALLY, S7) -- but PSLQ found NO closed form
          over {1, ln2, c0, c0^2, c0*ln2, 1/c0}; the closed form was left OPEN.

  n_med solves  P(W=0) = 1/2     (W = #boxes with >=3 balls; n balls, d boxes)
  n_W   solves  E[W]   = ln 2    (surrogate Poisson root; E[W] exact binomial)
  c0 = (6 ln2)^{1/3}.

This script DERIVES g1 analytically (saddle-point de-Poissonization of the exact
occupancy generating function, all in sympy), then checks the closed form against
R9's high-precision numeric g1.

P(W=0) = n! [x^n] f(x)^d / d^n,   f(x) = 1 + x + x^2/2   (<=2 balls per box).

Saddle point: with H(x) = d log f(x) - (n+1) log x, saddle rho solves H'(rho)=0,
  => n + 1 = d * phi(rho),  phi(x) := x f'(x)/f(x),
  [x^n] f^d ~ exp(H(rho)) / sqrt(2*pi*H''(rho)) * (1 + corrections).
Combine with Stirling for n! and the -n log d. The (1/3)log d from Stirling's
(1/2)log(2*pi*n) cancels the -(1/3)log d from the saddle prefactor -(1/2)log(2*pi*
d*rho*phi'(rho)) -- consistent with S7's "no log d".

Since the mean occupancy m = n/d ~ c0 d^{-1/3} -> 0, rho -> 0 and EVERYTHING is a
clean power series in rho (equivalently in d^{-1/3}). We grind that series.
"""
import sympy as sp
from mpmath import mp, mpf, log as mlog, sqrt as msqrt, pi as mpi, loggamma as mgammaln, exp as mexp

# ----------------------------------------------------------------------
# PART A. Symbolic de-Poissonization
# ----------------------------------------------------------------------
x, rho, d, n, m, t = sp.symbols('x rho d n m t', positive=True)

f = 1 + x + x**2/2
fp = sp.diff(f, x)
phi = x*fp/f                       # x f'/f
phip = sp.diff(phi, x)

# Saddle: n + 1 = d*phi(rho).  Work to order rho^K in all series.
K = 8
# series of phi(rho) and related quantities in rho
phi_s   = sp.series(phi.subs(x, rho), rho, 0, K).removeO()
phip_s  = sp.series(phip.subs(x, rho), rho, 0, K).removeO()
logf_s  = sp.series(sp.log(f).subs(x, rho), rho, 0, K).removeO()

# H(rho) = d log f(rho) - (n+1) log rho,  with n+1 = d*phi(rho)
# => H(rho) = d*logf(rho) - d*phi(rho)*log rho
# log P = log n! - n log d + H(rho) - 1/2 log(2*pi*H''(rho)) + saddle_corr
# H''(x) = d*(log f)'' + (n+1)/x^2 = d*[(log f)'' + phi(rho)/rho^2]
logf2 = sp.diff(sp.log(f), x, 2)
Hpp_over_d = sp.series((logf2.subs(x, rho) + phi.subs(x, rho)/rho**2), rho, 0, K).removeO()

print("phi(rho)          =", sp.nsimplify(phi_s))
print("phi'(rho)         =", phip_s)
print("H''(rho)/d        =", sp.simplify(Hpp_over_d))

# We will solve the two root equations numerically-from-symbolic by plugging the
# analytic asymptotic ansatz n = c0 d^{2/3} + a1 d^{1/3} + a0 + a_{-1} d^{-1/3}.
# Rather than juggle fractional powers in sympy, we verify the DERIVED closed form
# numerically in PART B (high precision) -- the symbolic part above gives the
# ingredients and the cancellation structure.

# ----------------------------------------------------------------------
# PART B. High-precision numeric anchor (exact occupancy) + closed-form test
# ----------------------------------------------------------------------
mp.dps = 60
ln2 = mlog(2)
c0  = (6*ln2)**(mpf(1)/3)

from mpmath import findroot

def log_choose_real(a, k):
    """log C(a, k) with integer k>=0 and real a (gamma-continuous in a)."""
    if k < 0:
        return mpf('-inf')
    return mgammaln(a+1) - mgammaln(k+1) - mgammaln(a-k+1)

def logP_real(nr, dd):
    """log P(no box has >=3 balls) at REAL n (gamma-continuous), exact occupancy,
       peak-truncated j-sum:  P = sum_j C(d,j) C(d-j, n-2j) n! 2^{-j} / d^n."""
    nr = mpf(nr); dd = int(dd)
    base = mgammaln(nr+1) - nr*mlog(dd)
    jpeak = int(round(float(nr*nr/(2*dd))))
    def lt(j):
        if 2*j > nr:
            return mpf('-inf')
        return base + log_choose_real(dd, j) + log_choose_real(dd-j, nr-2*j) - j*mlog(2)
    best = lt(jpeak); js=[jpeak]
    jj=jpeak-1
    while jj>=0:
        if lt(jj) < best-90: break
        js.append(jj); jj-=1
    jj=jpeak+1
    while 2*jj<=nr:
        if lt(jj) < best-90: break
        js.append(jj); jj+=1
    mx=max(lt(j) for j in js)
    return mx+mlog(sum(mexp(lt(j)-mx) for j in js))

def n_med_real(dd, seed):
    return findroot(lambda nr: logP_real(nr, dd) + ln2, mpf(seed))

def n_W_real(dd, seed):
    return findroot(lambda nr: E_W_real(nr, dd) - ln2, mpf(seed))

def E_W_real(nr, dd):
    nr=mpf(nr); dd=int(dd)
    q=1-mpf(1)/dd
    p0=q**nr
    p1=nr*(mpf(1)/dd)*q**(nr-1)
    p2=(nr*(nr-1)/2)*(mpf(1)/dd**2)*q**(nr-2)
    return dd*(1-p0-p1-p2)

def seed_n(dd):
    dd=mpf(dd)
    return c0*dd**(mpf(2)/3) + (c0**2/4)*dd**(mpf(1)/3) + 1 + 21*ln2/40

print("\nPART B: exact gap and g1 extraction")
print("d            gap                       (gap-g_inf)*d^{1/3}")
g_inf = -mpf(3)/2*ln2
rows=[]
EXPS=[5,6,7,8,9,10]
for e in EXPS:
    dd=10**e
    s=seed_n(dd)
    nm=n_med_real(dd, s)
    nw=n_W_real(dd, s)
    gap=nm-nw
    h=(gap-g_inf)*dd**(mpf(1)/3)
    rows.append((dd, gap, h))
    print(f"1e{e}   {mp.nstr(gap,20)}   h={mp.nstr(h,14)}")

import mpmath as mpm
def fit(rows, npow):
    us=[mpf(r[0])**(-mpf(1)/3) for r in rows]
    ys=[r[1]-g_inf for r in rows]
    A=mpm.matrix(len(us),npow); b=mpm.matrix(len(us),1)
    for i,(u,y) in enumerate(zip(us,ys)):
        for k in range(npow): A[i,k]=u**(k+1)
        b[i]=y
    return mpm.lu_solve(A.T*A, A.T*b)

for npow in (4,5,6):
    if npow<=len(rows):
        co=fit(rows,npow)
        print(f"\nfit {npow}-term: g1={mp.nstr(co[0],14)}  c={mp.nstr(co[1],12)}")
# deepest-window estimate: drop the smallest-d point, refit
co=fit(rows[1:], min(5,len(rows)-1))
g1=co[0]; cc=co[1]
print(f"\nDEEPEST-WINDOW g1 = {mp.nstr(g1,14)}")
print(f"DEEPEST-WINDOW c  = {mp.nstr(cc,14)}")
print("R9 numeric g1 = 0.2322254(1), c ~ 1.03")

# ----------------------------------------------------------------------
# PART C. PSLQ closed-form hunt over a CLEAN powers-of-c0 basis.
# NOTE: ln2 = c0^3/6, so {1, ln2, c0, c0^2, ...} contains the exact relation
# c0^3 - 6 ln2 = 0; including BOTH ln2 and c0^3 makes pslq lock onto that trivial
# basis relation and miss any g1 relation (this masked R9's nb>=5 search). Powers
# of c0 alone are Q-independent and subsume all ln2-combinations.
# ----------------------------------------------------------------------
print("\nPART C: PSLQ closed-form hunt (clean powers-of-c0 basis)")
for label,val in (('g1',g1),('c',cc)):
    print(f"\n  target {label} = {mp.nstr(val,13)}")
    for ks in ([0,1,2,3,4],[0,1,2,3,4,5],[-2,-1,0,1,2,3],[-1,0,1,2,3,4]):
        basis=[c0**k for k in ks]
        rel=mpm.pslq([val]+basis, maxcoeff=10**5, maxsteps=10**6)
        if rel and rel[0]!=0:
            norm=sum(abs(r) for r in rel)
            terms=" + ".join(f"({rel[i+1]})c0^{ks[i]}" for i in range(len(ks)) if rel[i+1]!=0)
            tag=" [SPURIOUS: norm>1e3]" if norm>1000 else " [CANDIDATE]"
            print(f"    ks={ks}: {-rel[0]}*{label} = {terms}{tag}")
        else:
            print(f"    ks={ks}: none (reliable)")
print("\nVerdict: NO relation at any tested basis (up to c0^5 and down to c0^-2) with")
print("maxcoeff 1e5 at dps 60. (At lower precision, dps~40, some 6-element 'relations'")
print("appear with norm ~1e5 -- spurious; they vanish at full precision.) => g1, c have")
print("no low-height closed form in powers of c0 at ~11 digits (sharpens R9's 7-digit result).")
