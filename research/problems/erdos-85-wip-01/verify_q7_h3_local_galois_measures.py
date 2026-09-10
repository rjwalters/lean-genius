#!/usr/bin/env python3
"""Exact fixed-H3 diagonal relaxation witness; no optimizer or graph claim."""
import json
from pathlib import Path
import sympy as s

x=s.symbols('x')
factors=[([1,-3],4),([1,2],4),([1,-1,-7],1),([1,0,-6],4),([1,1,-7],2),([1,1,-5],10)]
roots=[]; multiplicities=[]; pairs=[]; linear=[]
for coeff,m in factors:
    rr=sorted(s.solve(s.Poly.from_list(coeff,x).as_expr(),x),key=lambda r:float(r))
    if len(rr)==1: linear.append(len(roots))
    else: pairs.append((len(roots),len(roots)+1,coeff[1]**2-4*coeff[2]))
    roots.extend(rr);multiplicities.extend([m]*len(rr))
Z=s.eye(10)
for lo,hi,d in pairs:
    Z[lo,lo]=Z[hi,lo]=1
    Z[lo,hi]=-s.sqrt(d);Z[hi,hi]=s.sqrt(d)
M=(s.Matrix([[r**j for r in roots] for j in range(7)])*Z).applyfunc(s.simplify)
assert all(a.is_Rational for a in M)
assert [s.simplify(sum(m*r**j for m,r in zip(multiplicities,roots))) for j in range(1,7)]==[-7,255,-106,1767,-947,13470]
Q=s.Matrix([[7,3],[-1,0]]);Gi=s.Matrix([[46,24],[24,30]]).inv()

def target(t,tau,R,delta):
    u=s.Matrix([[1,t]])
    q=[(u*Q**j*Gi*u.T)[0] for j in range(7)]
    z=s.Rational(t*(3-t),21)
    a=[1-q[0]-z,-q[1],7-t-q[2],2*tau-q[3],(7-t)*(13-t)-3-q[4]]
    cd2=(u*Q*(Q-s.eye(2))**2*Gi*u.T)[0]
    dq3=(u*(Q-s.eye(2))**3*Gi*u.T)[0]
    a.append(R+12*a[3]-36*a[1]-cd2)
    a.append(216*a[0]-108*a[2]+18*a[4]+dq3-z-2*delta)
    return s.Matrix(a)

profiles=json.loads(Path(__file__).with_name('q7_h3_local_galois_measures.json').read_text())
assert set(profiles)=={'pair','triple'}
for name,census in [('pair',[25,18,3,0]),('triple',[24,21,0,1])]:
    counts=[0]*4;totals=[0]*3;mass=s.zeros(10,1)
    for item in profiles[name]['types']:
        a=item['type'];t,tau,R,delta=(a[k] for k in ['t','tau','R','delta'])
        n=item['count'];assert isinstance(n,int) and n>0
        assert all(isinstance(v,int) for v in [t,tau,R,delta])
        assert 0<=t<=3 and 0<=tau<=3 and 0<=7-2*t-2*tau<=6-t
        survivors=t+2*tau-1
        assert 0<=survivors<=5 and R%2==0 and 0<=R<=2*[0,0,1,3,4,6][survivors]
        assert 0<=delta<=min(18,(6-t)*(5-t)//2)
        w=s.Matrix([s.Rational(v) for v in item['aggregate_rational_coordinates']])
        assert w.shape==(10,1)
        assert all(w[k]>=0 for k in linear)
        for lo,hi,d in pairs:
            assert (w[lo]==0 and w[hi]==0) or (w[lo]>0 and w[lo]**2>d*w[hi]**2)
        assert M*w==n*target(t,tau,R,delta)
        counts[t]+=n
        for j,v in enumerate([tau,R,delta]):totals[j]+=n*v
        mass+=w
    expected=s.Matrix(multiplicities)
    for lo,hi,d in pairs:expected[hi]=0
    assert mass==expected
    assert counts==census and totals==[87,274,18]
    print(name+': PASS exact rational conjugate weights, local moments 0..6, census and global multiplicities')
print('Scope: diagonal necessary-condition relaxation only; no off-diagonal/projector/graph realization.')
