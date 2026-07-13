#!/usr/bin/env python3
"""
Driver: validate the symbolic A(rho,eps) saddle de-Poissonization against EXACT
occupancy numerics, then solve A=ln2 and E[W]=ln2 as asymptotic series in
D=d^{1/3} to extract g_inf, g1, c in closed form.  (researcher-2, S9)
"""
import sympy as sp
import importlib.util, sys, os

HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location(
    "saddle", os.path.join(HERE, "verify_birthday_oq03_g1_saddle_symbolic.py"))
saddle = importlib.util.module_from_spec(spec)
spec.loader.exec_module(saddle)

A   = saddle.A
rho = saddle.rho
eps = saddle.eps
phi_s = saddle.phi_s

# =====================================================================
# PART 0. VALIDATE symbolic A against exact -log P(no triple).
# =====================================================================
from mpmath import mp, mpf, log as mlog, exp as mexp, loggamma as mgammaln
mp.dps = 50

def log_choose_real(a, k):
    if k < 0: return mpf('-inf')
    return mgammaln(a+1) - mgammaln(k+1) - mgammaln(a-k+1)

def logP_real(nr, dd):
    """exact log P(no box >=3 balls), real n, peak-truncated j-sum."""
    nr = mpf(nr); dd = int(dd)
    base = mgammaln(nr+1) - nr*mlog(dd)
    jpk = int(round(float(nr*nr/(2*dd))))
    def lt(j):
        if 2*j > nr: return mpf('-inf')
        return base + log_choose_real(dd, j) + log_choose_real(dd-j, nr-2*j) - j*mlog(2)
    best = lt(jpk); js=[jpk]; jj=jpk-1
    while jj>=0:
        if lt(jj) < best-100: break
        js.append(jj); jj-=1
    jj=jpk+1
    while 2*jj<=nr:
        if lt(jj) < best-100: break
        js.append(jj); jj+=1
    mx=max(lt(j) for j in js)
    return mx+mlog(sum(mexp(lt(j)-mx) for j in js))

# lambdify A and phi for numeric evaluation
A_f   = sp.lambdify((rho, eps), A, 'mpmath')
phi_f = sp.lambdify((rho, eps), phi_s, 'mpmath')

print("=== VALIDATION: symbolic A vs exact -logP (n = d*phi(rho)-1) ===")
print("d        rho        n=d*phi-1        A_sym            -logP_exact      diff")
for e, rv in [(6, '0.012'), (6,'0.016'), (7,'0.007'), (8,'0.0035'), (9,'0.0016')]:
    dd = 10**e
    epv = mpf(1)/dd
    rv = mpf(rv)
    nval = dd*phi_f(rv, epv) - 1
    Asym = A_f(rv, epv)
    Aexc = -logP_real(nval, dd)
    print(f"1e{e}  {mp.nstr(rv,5)}  {mp.nstr(nval,12)}  {mp.nstr(Asym,14)}  {mp.nstr(Aexc,14)}  {mp.nstr(Asym-Aexc,4)}")

# =====================================================================
# PART 1. Asymptotic solve of A(rho,eps)=ln2 as a series in X = d^{-1/3}.
#   d = X^{-3}, eps = X^3, rho = sum_{k>=1} r_k X^k.
#   coeff(A, X^0) = ln2  -> r_1;  coeff(A, X^j)=0 (j>=1) -> r_{j+1}.
# Keep symbolic with L = ln2, c0 = (6L)^{1/3}, c0^3 -> 6L.
# =====================================================================
print("\n=== PART 1: asymptotic solve A = ln2 ===")
X = sp.symbols('X', positive=True)
L = sp.symbols('L', positive=True)            # L = ln 2
c0 = sp.symbols('c0', positive=True)          # c0 = (6L)^{1/3}, c0^3 = 6 L
NN = 7                                         # number of r_k unknowns
rks = sp.symbols('r1:%d' % (NN+1))            # r1..r7

def c0reduce(expr):
    """Reduce powers of c0 using c0^3 = 6L (keeps closed form compact)."""
    expr = sp.expand(expr)
    # repeatedly replace c0**3 -> 6L
    p = sp.Wild('p')
    for k in range(12, 2, -1):
        q, rem = divmod(k, 3)
        expr = expr.subs(c0**k, (6*L)**q * c0**rem)
    return sp.expand(expr)

ORDER = 6   # expand A through X^ORDER (need X^3 for g1, X^4 for c)
rho_series = sum(rks[k]*X**(k+1) for k in range(NN))

# Substitute into A and series in X.  Use the validated module-level A.
A_sub = A.subs(eps, X**3).subs(rho, rho_series)
A_ser = sp.series(A_sub, X, 0, ORDER+1).removeO()
A_poly = sp.Poly(sp.expand(A_ser), X)

sol = {}
# order X^0: r1
c_of = {}
for j in range(0, ORDER+1):
    c_of[j] = A_poly.coeff_monomial(X**j)

# r1 from X^0 = L
eq0 = c_of[0].subs(sol) - L
r1sol = sp.solve(eq0, rks[0])
# pick the real positive cube root branch = c0
print("X^0 eq:", sp.simplify(eq0), " -> r1 solutions:", r1sol)
sol[rks[0]] = c0           # define r1 := c0 ; (c0^3 = 6L makes r1^3/6 = L)

for j in range(1, ORDER):
    cj = sp.expand(c_of[j].subs(sol))
    cj = c0reduce(cj)
    # cj is linear in r_{j+1}
    rnext = rks[j]
    a1 = cj.coeff(rnext, 1)
    a0 = cj.coeff(rnext, 0)
    if a1 == 0:
        print(f"  X^{j}: coeff of {rnext} vanished; eq={cj}")
        continue
    val = c0reduce(sp.together(-a0/a1))
    sol[rnext] = sp.simplify(val)
    print(f"  r{j+1} = {sol[rnext]}")


# =====================================================================
# PART 2. n_med = d*phi(rho) - 1 = phi(rho_sol)/X^3 - 1  (Laurent in X).
# =====================================================================
print("\n=== PART 2: n_med series ===")
rho_sol = sum(sol[rks[k]]*X**(k+1) for k in range(NN) if rks[k] in sol)
phi_rho = sp.series(phi_s.subs(rho, rho_sol), X, 0, ORDER+1).removeO()
n_med = sp.expand(phi_rho/X**3 - 1)
n_med = c0reduce(n_med)
# collect coefficients by powers of X (Laurent: X^{-2}..)
n_med_poly = sp.Poly(sp.expand(n_med*X**2), X)   # clear the X^{-2}
def lc(poly_shifted, k, shift):
    return c0reduce(poly_shifted.coeff_monomial(X**(k+shift)))
print("n_med coefficients (coef of D^j = X^{-j}):")
nmed_co = {}
for power in range(-2, ORDER-1):   # X^power
    co = c0reduce(n_med_poly.coeff_monomial(X**(power+2)))
    nmed_co[power] = sp.simplify(co)
    if co != 0:
        print(f"  X^{power} (D^{-power}): {nmed_co[power]}")

# =====================================================================
# PART 3. Solve E[W] = ln2 for n_W as Laurent series in X.
#   E[W] = d*P(Bin(n,1/d)>=3),  p=eps=X^3,  q=1-eps,  m=n*eps.
# =====================================================================
print("\n=== PART 3: solve E[W]=ln2 for n_W ===")
KK = ORDER
bks = {k: sp.symbols(f'b_{k+2}') for k in range(-2, KK)}   # b for X^k, k=-2..KK-1
n_W_ser = sum(bks[k]*X**k for k in range(-2, KK))
logq = sp.series(sp.log(1 - X**3), X, 0, KK+6).removeO()
n_logq = sp.expand(n_W_ser*logq)
qn = sp.series(sp.exp(n_logq), X, 0, KK+1).removeO()       # q^n
inv_q  = sp.series(1/(1-X**3), X, 0, KK+6).removeO()
qn1 = sp.expand(qn*inv_q)                                   # q^{n-1}
qn2 = sp.expand(qn*inv_q*inv_q)                             # q^{n-2}
eps = X**3
term = 1 - qn - n_W_ser*eps*qn1 - (n_W_ser*(n_W_ser-1)/2)*eps**2*qn2
EW = sp.series(sp.expand(term/eps), X, 0, KK+1).removeO()
EW_poly = sp.Poly(sp.expand(EW), X)

solW = {}
# X^0 coeff = L -> b_{-2}
e0 = EW_poly.coeff_monomial(X**0)
print("EW X^0 eq:", sp.simplify(e0), "= L")
solW[bks[-2]] = c0
for power in range(1, KK-1):
    cj = c0reduce(sp.expand(EW_poly.coeff_monomial(X**power).subs(solW)))
    target = bks[power-2]   # b for X^{power-2}? no: unknown freed at this order is b_{power-2}
    # the X^power equation introduces b_{power-2} linearly
    unk = bks[power-2]
    a1 = cj.coeff(unk, 1); a0 = cj.coeff(unk, 0)
    if a1 == 0:
        print(f"  EW X^{power}: coeff of {unk} vanished; eq={cj}")
        continue
    solW[unk] = sp.simplify(c0reduce(sp.together(-a0/a1)))
    print(f"  b for X^{power-2} (n_W coef of D^{-(power-2)}): {solW[unk]}")

# =====================================================================
# PART 4. gap = n_med - n_W ;  read off g_inf, g1, c (closed form).
# =====================================================================
print("\n=== PART 4: gap = n_med - n_W  (closed-form coefficients) ===")
nW_co = {}
nW_co[-2] = c0
for power in range(1, KK-1):
    unk = bks[power-2]
    if unk in solW:
        nW_co[power-2] = solW[unk]
gap_co = {}
for p in sorted(set(list(nmed_co.keys()) + list(nW_co.keys()))):
    g = c0reduce(sp.expand(nmed_co.get(p,0) - nW_co.get(p,0)))
    gap_co[p] = sp.simplify(g)

names = {0:'g_inf', 1:'g1', 2:'c'}
for p in sorted(gap_co):
    label = names.get(p, f'X^{p}')
    print(f"  gap[X^{p}] ({label}) = {gap_co[p]}")

# substitute L=ln2, c0=(6L)^{1/3} numerically
from mpmath import mp, mpf, log as mlog
mp.dps = 40
Lval = mlog(2); c0val = (6*Lval)**(mpf(1)/3)
def numval(expr):
    return sp.lambdify((), expr.subs({L:sp.Float(str(Lval),40), c0:sp.Float(str(c0val),40)}), 'mpmath')()
print("\nNumeric values:")
print(f"  g_inf = {mp.nstr(numval(gap_co.get(0,0)),16)}   (target -1.5 ln2 = {mp.nstr(-mpf(3)/2*Lval,16)})")
print(f"  g1    = {mp.nstr(numval(gap_co.get(1,0)),16)}   (target 0.2322254...)")
print(f"  c     = {mp.nstr(numval(gap_co.get(2,0)),16)}   (target ~1.03)")

print("\nClosed forms (L=ln2, c0=(6 ln2)^{1/3}):")
print("  g_inf =", sp.nsimplify(gap_co.get(0,0), [L]))
print("  g1    =", gap_co.get(1,0))
print("  c     =", gap_co.get(2,0))
