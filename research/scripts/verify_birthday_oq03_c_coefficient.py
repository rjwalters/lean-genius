#!/usr/bin/env python3
"""
birthday-problem-oq-03-oq-01-oq-02-oq-02 -- closed form for the d^{-2/3} gap
coefficient `c` (researcher-7, S10).

Gap expansion (k=3 triple-birthday median threshold):

    gap(d) := n_med(d) - n_W(d)
            = g_inf + g1 d^{-1/3} + c d^{-2/3} + O(d^{-1}),

  g_inf = -(3/2) ln2 = -c0^3/4            (S5, settled),
  g1    = (5/24) c0 ln2 = 5*6^{1/3}(ln2)^{4/3}/24   (S9 / PR #24729, settled),
  c     = c0^2 (3/4 - (61/120) ln2) = 6^{2/3}(ln2)^{2/3}(90 - 61 ln2)/120
        = 1.0283769358...   (this session, S10 -- was OPEN before),
  g3    = 21 ln2 (19 ln2 - 40)/160 = -2.4408929945...  (d^{-1} coeff, bonus),
  c0    = (6 ln2)^{1/3}.

n_med(d) solves -log P(no triple) = ln2, where
  P(no triple) = n! d^{-n} [w^n] f(w)^d,   f(w) = 1 + w + w^2/2.
n_W(d) solves E[W] = ln2, E[W] = d * P(Bin(n,1/d) >= 3) (exact binomial).

This script is SELF-CONTAINED (it does not import S9's saddle module, which lives
on the still-unmerged PR #24729). It rebuilds the validated symbolic saddle
exponent A(rho,eps), solves A=ln2 and E[W]=ln2 as asymptotic series in
X = d^{-1/3} to sufficient depth, performs a FULL back-substitution of the
higher series coefficients (S9's driver solved them sequentially without
back-substituting, which left `c` contaminated by the undetermined n_W
coefficients b_5,b_6 -- THE reason `c` was reported "open"), and reads off the
closed form for `c`.  A high-precision exact-occupancy gap computation confirms
the value.

Saddle background (S8/S9): for [w^n] f^d, G(w) = d log f - (n+1) log w,
  G'(rho)=0 => n+1 = d*phi(rho), phi = w f'/f.  The 1/2-log and first saddle
  correction `corr1 = G4/(8 G2^2) - 5 G3^2/(24 G2^3)` are O(eps) and first
  enter A at order X^2 = d^{-2/3} -- exactly the order of `c` -- so corr1 is the
  COMPLETE saddle correction needed for c (corr2 ~ X^3).
"""
import sympy as sp

# =====================================================================
# PART A. Rebuild the symbolic saddle exponent A(rho, eps).  (= S9's module)
# =====================================================================
w, rho, eps = sp.symbols('w rho epsilon', positive=True)  # eps = 1/d
KMAX = 12  # series order in rho

f   = 1 + w + w**2/2
fp  = sp.diff(f, w)
phi = w*fp/f
logf = sp.log(f)

def ser(expr):
    return sp.series(expr.subs(w, rho), rho, 0, KMAX).removeO()

phi_s  = ser(phi)
logf2  = sp.diff(logf, w, 2)
logf3  = sp.diff(logf, w, 3)
logf4  = sp.diff(logf, w, 4)
N_expr = logf2.subs(w, rho) + phi.subs(w, rho)/rho**2     # G''*eps, analytic*1/rho

# saddle G-derivative brackets (the eps-free parts; Gk = (1/eps)*bracket)
Gk2 = logf2.subs(w, rho) + phi.subs(w, rho)/rho**2
Gk3 = logf3.subs(w, rho) - 2*phi.subs(w, rho)/rho**3
Gk4 = logf4.subs(w, rho) + 6*phi.subs(w, rho)/rho**4
E1  = Gk4/(8*Gk2**2) - sp.Rational(5, 24)*Gk3**2/Gk2**3   # corr1/eps
E1_s = sp.series(E1, rho, 0, KMAX).removeO()

BR   = phi*(sp.log(f) - sp.log(fp) + 1) - sp.log(f)        # extensive part (* d)
BR_s = ser(BR)                                             # starts at rho^3
phiN = (phi*N_expr).subs(w, rho)
logQ0_s = sp.series(sp.Rational(1, 2)*sp.log(phiN), rho, 0, KMAX).removeO()
inv_phi = sp.series((f/(rho*fp)).subs(w, rho), rho, 0, KMAX).removeO()  # 1/phi

# A = d*BR + 1/2 log(phi*N) - (1/12) eps/phi - eps*E1.
# (All log d cancels; the eps-correction collapse to -(1/12)u is verified in S9.)
A = sp.expand(BR_s/eps + logQ0_s - sp.Rational(1, 12)*eps*inv_phi - eps*E1_s)

# =====================================================================
# PART B. Asymptotic solve A = ln2 for n_med.
# =====================================================================
X  = sp.symbols('X', positive=True)            # X = d^{-1/3}
L  = sp.symbols('L', positive=True)            # L = ln 2
c0 = sp.symbols('c0', positive=True)           # c0 = (6L)^{1/3}, c0^3 = 6L

def c0reduce(expr):
    expr = sp.expand(expr)
    for k in range(15, 2, -1):
        q, rem = divmod(k, 3)
        expr = expr.subs(c0**k, (6*L)**q * c0**rem)
    return sp.expand(expr)

ORDER = 6          # expand through X^ORDER; with KK=ORDER+2 the n_W solve reaches
                   # X^4 (b_5,b_6), enough to make c free of undetermined symbols
NN    = ORDER + 3
rks   = sp.symbols('r1:%d' % (NN+1))
rho_series = sum(rks[k]*X**(k+1) for k in range(NN))

A_sub  = A.subs(eps, X**3).subs(rho, rho_series)
A_ser  = sp.series(A_sub, X, 0, ORDER+1).removeO()
A_poly = sp.Poly(sp.expand(A_ser), X)

sol = {rks[0]: c0}                              # r1 = c0 (from X^0 eq r1^3/6 = L)
for j in range(1, ORDER):
    cj = c0reduce(sp.expand(A_poly.coeff_monomial(X**j).subs(sol)))
    rnext = rks[j]
    a1 = cj.coeff(rnext, 1); a0 = cj.coeff(rnext, 0)
    if a1 == 0:
        continue
    sol[rnext] = sp.simplify(c0reduce(sp.together(-a0/a1)))

rho_sol = sum(sol.get(rks[k], 0)*X**(k+1) for k in range(NN))
phi_rho = sp.series(phi_s.subs(rho, rho_sol), X, 0, ORDER+1).removeO()
n_med   = c0reduce(sp.expand(phi_rho/X**3 - 1))
n_med_poly = sp.Poly(sp.expand(n_med*X**2), X)
nmed_co = {p: c0reduce(n_med_poly.coeff_monomial(X**(p+2))) for p in range(-2, ORDER-1)}

# =====================================================================
# PART C. Asymptotic solve E[W] = ln2 for n_W (deep + back-substitution).
# =====================================================================
KK  = ORDER + 2                                 # deep enough to fix b at X^3,X^4
bks = {k: sp.symbols(f'b_{k+2}') for k in range(-2, KK)}
n_W_ser = sum(bks[k]*X**k for k in range(-2, KK))
logq  = sp.series(sp.log(1 - X**3), X, 0, KK+8).removeO()
qn    = sp.series(sp.exp(n_W_ser*logq), X, 0, KK+1).removeO()
inv_q = sp.series(1/(1 - X**3), X, 0, KK+8).removeO()
qn1   = sp.expand(qn*inv_q)
qn2   = sp.expand(qn*inv_q*inv_q)
epsX  = X**3
term  = 1 - qn - n_W_ser*epsX*qn1 - (n_W_ser*(n_W_ser-1)/2)*epsX**2*qn2
EW    = sp.series(sp.expand(term/epsX), X, 0, KK+1).removeO()
EW_poly = sp.Poly(sp.expand(EW), X)

solW = {bks[-2]: c0}                            # X^0 eq: b_{-2}^3/6 = L
for power in range(1, KK-1):
    unk = bks[power-2]
    cj = c0reduce(sp.expand(EW_poly.coeff_monomial(X**power).subs(solW)))
    a1 = cj.coeff(unk, 1); a0 = cj.coeff(unk, 0)
    if a1 == 0:
        continue
    solW[unk] = sp.simplify(c0reduce(sp.together(-a0/a1)))

# FULL back-substitution: resolve every b coefficient against all the others
# (S9 solved sequentially and never back-substituted -> b_5,b_6 leaked into c).
for _ in range(6):
    changed = False
    for k in list(solW):
        new = c0reduce(sp.expand(solW[k].subs(solW)))
        if new != solW[k]:
            solW[k] = new; changed = True
    if not changed:
        break
nW_co = {p: c0reduce(sp.expand(solW.get(bks[p], 0))) for p in range(-2, KK)}

# =====================================================================
# PART D. gap = n_med - n_W ; read off g_inf, g1, c (closed form).
# =====================================================================
gap_co = {}
for p in range(-2, ORDER-1):
    gap_co[p] = sp.simplify(c0reduce(sp.expand(nmed_co.get(p, 0) - nW_co.get(p, 0))))

names = {-2: 'X^-2', -1: 'X^-1', 0: 'g_inf', 1: 'g1', 2: 'c', 3: 'X^3'}
print("=== gap coefficients (L = ln2, c0 = (6L)^{1/3}, c0^3 = 6L) ===")
for p in sorted(gap_co):
    free = gap_co[p].free_symbols - {L, c0}
    flag = ''  if not free else f'   <-- UNRESOLVED {free}'
    print(f"  gap[X^{p}] ({names.get(p, '')}) = {gap_co[p]}{flag}")

c_sym = gap_co[2]
print("\n=== closed form for c ===")
print("  c =", c_sym)
print("  c (factored) =", sp.factor(c_sym))

# numeric value
from mpmath import mp, mpf, log as mlog
mp.dps = 40
Lval = mlog(2); c0val = (6*Lval)**(mpf(1)/3)
subs_num = {L: sp.Float(str(Lval), 40), c0: sp.Float(str(c0val), 40)}
def numval(expr):
    return sp.lambdify((), expr.subs(subs_num), 'mpmath')()
print("\nNumeric check (closed forms vs known targets):")
print(f"  g_inf = {mp.nstr(numval(gap_co[0]),16)}   target -1.5 ln2 = {mp.nstr(-mpf(3)/2*Lval,16)}")
print(f"  g1    = {mp.nstr(numval(gap_co[1]),16)}   target 0.2322254398566682")
print(f"  c     = {mp.nstr(numval(c_sym),16)}   (S7 4-term numeric fit gave ~1.03)")

# =====================================================================
# PART E. Independent numeric check: exact-occupancy gap, fit c directly.
#   gap(d) = n_med_real(d) - n_W(d).  Subtract the now-known g_inf + g1 X,
#   divide by X^2; the limit is c.
# =====================================================================
from mpmath import exp as mexp, loggamma as mgammaln, findroot, mpf as MPF
mp.dps = 50

def log_choose_real(a, k):
    if k < 0: return mpf('-inf')
    return mgammaln(a+1) - mgammaln(k+1) - mgammaln(a-k+1)

def logP_no_triple(nr, dd):
    """exact log P(no box >= 3 balls): n! d^{-n}[w^n](1+w+w^2/2)^d, peak-trunc j-sum."""
    nr = mpf(nr); dd = int(dd)
    base = mgammaln(nr+1) - nr*mlog(dd)
    jpk = int(round(float(nr*nr/(2*dd))))
    def lt(j):
        if 2*j > nr: return mpf('-inf')
        return base + log_choose_real(dd, j) + log_choose_real(dd-j, nr-2*j) - j*mlog(2)
    best = lt(jpk); js = [jpk]; jj = jpk-1
    while jj >= 0:
        if lt(jj) < best-120: break
        js.append(jj); jj -= 1
    jj = jpk+1
    while 2*jj <= nr:
        if lt(jj) < best-120: break
        js.append(jj); jj += 1
    mx = max(lt(j) for j in js)
    return mx + mlog(sum(mexp(lt(j)-mx) for j in js))

def EW_exact(nr, dd):
    """E[W] = d*P(Bin(n,1/d)>=3), exact, real n."""
    nr = mpf(nr); dd = int(dd); p = mpf(1)/dd; q = 1-p
    lpk = lambda k: log_choose_real(nr, k) + k*mlog(p) + (nr-k)*mlog(q)
    P012 = mexp(lpk(0)) + mexp(lpk(1)) + mexp(lpk(2))
    return dd*(1 - P012)

Lm = mlog(2); c0m = (6*Lm)**(mpf(1)/3)
g_inf_m = -mpf(3)/2*Lm
g1_m  = mpf(5)/24*c0m*Lm
c_pred  = numval(c_sym)
g3_pred = numval(gap_co.get(3, sp.Integer(0)))   # closed-form d^{-1} coefficient
n0 = lambda dd: c0m*mpf(dd)**(mpf(2)/3)

# c1 = (gap - g_inf - g1 X)/X^2  ->  c + g3 X + O(X^2).
# c2 = c1 - g3_pred X  removes the predicted d^{-1} term; if BOTH c and g3 are
# right, c2 is flat -> c (joint confirmation).  A 2-pt Richardson on c1 also -> c.
print("\n=== exact-occupancy gap vs predicted c (closed form c = %s) ===" % mp.nstr(c_pred, 12))
print("    g3 (d^{-1} coeff, also closed form) =", mp.nstr(g3_pred, 12))
print(" d      gap              c1=(gap-ginf-g1X)/X^2   c2=c1-g3*X")
rows = []
for e in [5, 6, 7]:
    dd = 10**e; X_ = mpf(dd)**(-mpf(1)/3)
    n_med = findroot(lambda nr: -logP_no_triple(nr, dd) - Lm, n0(dd))
    n_W   = findroot(lambda nr: EW_exact(nr, dd) - Lm, n0(dd))
    gap = n_med - n_W
    c1 = (gap - g_inf_m - g1_m*X_)/X_**2
    c2 = c1 - g3_pred*X_
    rows.append((e, X_, c1));
    print(f" 1e{e}  {mp.nstr(gap,12)}   {mp.nstr(c1,12)}        {mp.nstr(c2,12)}")

(ea, Xa, c1a), (eb, Xb, c1b) = rows[-2], rows[-1]
c_rich = (c1a*Xb - c1b*Xa)/(Xb - Xa)
print(f"\n2-pt Richardson of c1 (1e{ea},1e{eb}) -> {mp.nstr(c_rich,12)}   closed form {mp.nstr(c_pred,12)}")
print(f"|c_rich - c_closed| = {mp.nstr(abs(c_rich - c_pred),4)}")
print("c2 column flattening onto the closed form jointly confirms c AND g3.")
