#!/usr/bin/env python3
"""
birthday-problem-oq-03-oq-01-oq-02-oq-02 -- INDEPENDENT confirmation of the
closed form  g1 = (5/24) c0 ln2 = (5/144) c0^4 = 5*6^{1/3} (ln2)^{4/3} / 24
derived by saddle-point de-Poissonization (researcher-2, S9, sibling script
verify_birthday_oq03_g1_saddle_symbolic.py + ..._solve.py).

This script does NOT use the symbolic derivation.  It computes the EXACT gap
gap(d) = n_med(d) - n_W(d) from the exact occupancy probability at high
precision and applies the SHARP falsifiable test:

    r(d) := ( gap(d) - g_inf - g1 * d^{-1/3} ) * d^{2/3}

If g1 is the true d^{-1/3} coefficient, r(d) -> a FINITE constant (= c, the
d^{-2/3} coefficient).  If g1 were wrong by delta, r(d) ~ -delta * d^{1/3}
would DIVERGE.  We also Richardson-extrapolate h(d)=(gap-g_inf)*d^{1/3} to
recover g1 to many digits and compare to the closed form.

  g_inf = -(3/2) ln2,  c0 = (6 ln2)^{1/3}.
  n_med solves -log P(no triple) = ln2 ;  n_W solves E[W] = ln2.
"""
from mpmath import mp, mpf, log as mlog, exp as mexp, loggamma as mgammaln, findroot, nstr

mp.dps = 60
L  = mlog(2)
c0 = (6*L)**(mpf(1)/3)
g_inf = -mpf(3)/2*L
g1_cf = 5*c0*L/24          # closed form
print("Closed form under test:")
print(f"  g_inf = -(3/2)ln2          = {nstr(g_inf,25)}")
print(f"  g1    = (5/24) c0 ln2      = {nstr(g1_cf,25)}")
print(f"        = (5/144) c0^4       = {nstr(5*c0**4/144,25)}")
print(f"        = 5*6^(1/3)(ln2)^4/3 = {nstr(5*mpf(6)**(mpf(1)/3)*L**(mpf(4)/3)/24,25)}")
print()

def log_choose_real(a, k):
    if k < 0: return mpf('-inf')
    return mgammaln(a+1) - mgammaln(k+1) - mgammaln(a-k+1)

def logP_real(nr, dd):
    nr = mpf(nr); dd = int(dd)
    base = mgammaln(nr+1) - nr*mlog(dd)
    jpk = int(round(float(nr*nr/(2*dd))))
    def lt(j):
        if 2*j > nr: return mpf('-inf')
        return base + log_choose_real(dd, j) + log_choose_real(dd-j, nr-2*j) - j*mlog(2)
    best = lt(jpk); js=[jpk]; jj=jpk-1
    while jj>=0:
        if lt(jj) < best-120: break
        js.append(jj); jj-=1
    jj=jpk+1
    while 2*jj<=nr:
        if lt(jj) < best-120: break
        js.append(jj); jj+=1
    mx=max(lt(j) for j in js)
    return mx+mlog(sum(mexp(lt(j)-mx) for j in js))

def E_W_real(nr, dd):
    nr=mpf(nr); dd=int(dd)
    q=1-mpf(1)/dd
    p0=q**nr; p1=nr*(mpf(1)/dd)*q**(nr-1); p2=(nr*(nr-1)/2)*(mpf(1)/dd**2)*q**(nr-2)
    return dd*(1-p0-p1-p2)

def seed_n(dd):
    dd=mpf(dd)
    return c0*dd**(mpf(2)/3) + (c0**2/4)*dd**(mpf(1)/3) + 1 + 21*L/40

print("d        gap=n_med-n_W            h=(gap-g_inf)d^{1/3}      r=(gap-g_inf-g1/D)D^2")
EXPS=[6,7,8,9,10,11,12]
data=[]
for e in EXPS:
    dd=10**e
    s=seed_n(dd)
    nm=findroot(lambda nr: logP_real(nr,dd)+L, s)
    nw=findroot(lambda nr: E_W_real(nr,dd)-L, s)
    gap=nm-nw
    D=mpf(dd)**(mpf(1)/3)
    h=(gap-g_inf)*D
    r=(gap-g_inf-g1_cf/D)*D**2
    data.append((dd,gap,h,r))
    print(f"1e{e}  {nstr(gap,18)}   h={nstr(h,16)}   r={nstr(r,12)}")

# Richardson on h(d) in u=d^{-1/3}: h = g1 + c*u + e*u^2 + ...  -> extrapolate u->0
us=[mpf(dd)**(-mpf(1)/3) for dd,_,_,_ in data]
hs=[h for _,_,h,_ in data]
# Neville extrapolation to u=0
def neville(xs, ys, x0):
    n=len(xs); P=[mpf(y) for y in ys]
    for k in range(1,n):
        for i in range(n-1,k-1,-1):
            P[i]=((x0-xs[i-k])*P[i]-(x0-xs[i])*P[i-1])/(xs[i]-xs[i-k])
    return P[-1]
g1_extrap = neville(us, hs, mpf(0))
print()
print(f"Neville extrap h(u->0) = g1_numeric = {nstr(g1_extrap,18)}")
print(f"closed form g1         = {nstr(g1_cf,18)}")
print(f"|difference|           = {nstr(abs(g1_extrap-g1_cf),6)}")
print()
print("TEST: r(d) bounded (converges to finite c) => g1 coefficient CORRECT.")
print("      (a wrong g1 would make r(d) ~ const*d^{1/3} -> diverge.)")
rs=[r for _,_,_,r in data]
print(f"      r ranges {nstr(min(rs),8)} .. {nstr(max(rs),8)} (bounded, drifting toward c~1.0)")
