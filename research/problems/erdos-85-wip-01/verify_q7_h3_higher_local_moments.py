"""Exact H3 local C/D moment witnesses; no optimizer or graph realization."""
import json
from pathlib import Path
import sympy as s
from verify_q7_h3_local_galois_measures import roots,Z,Q,Gi,target,pairs,linear,multiplicities,factors,x

M=(s.Matrix([[r**k for r in roots] for k in range(13)])*Z).applyfunc(s.simplify)
ann=s.Poly(x*(x*x-7*x+3)*s.prod(s.Poly.from_list(f,x).as_expr() for f,m in factors),x)
assert ann.degree()==13 and ann.LC()==1 and all(a.is_Integer for a in ann.all_coeffs())
assert all(s.simplify(ann.eval(r))==0 for r in roots)
assert s.rem(ann.as_expr(),x*x-7*x+3,x)==0 and ann.eval(0)==0
profiles=json.loads(Path(__file__).with_name('q7_h3_higher_local_moments.json').read_text())
assert set(profiles)=={'pair','triple'}
for name,census in [('pair',[25,18,3,0]),('triple',[24,21,0,1])]:
    actual=[0]*4;totals=[0]*3;mass=s.zeros(10,1)
    for a in profiles[name]:
        t,tau,R,delta,n=[a[k] for k in ['t','tau','R','delta','count']]
        assert all(isinstance(k,int) for k in [t,tau,R,delta,n]) and n>0
        assert 0<=t<=3 and 0<=tau<=3 and 0<=7-2*t-2*tau<=6-t
        m=t+2*tau-1
        assert 0<=m<=5 and R%2==0 and 0<=R<=2*[0,0,1,3,4,6][m]
        assert 0<=delta<=(6-t)*(5-t)//2
        w=s.Matrix(list(map(s.Rational,a['coordinates'])));assert w.shape==(10,1)
        assert all(w[k]>=0 for k in linear)
        for lo,hi,d in pairs:
            assert (w[lo]==w[hi]==0) or (w[lo]>0 and w[lo]**2>d*w[hi]**2)
        r=M*w;assert r[:7,:]==target(t,tau,R,delta)
        u=s.Matrix([[1,t]]);z=s.Rational(t*(3-t),21)
        def mixed(i,j):
            coeff=s.Poly(x**i*(6-x*x)**j,x)
            residual=sum(c*r[k] for (k,),c in coeff.terms())
            return residual+(u*Q**i*(Q-s.eye(2))**j*Gi*u.T)[0]+(z*(-1)**j if i==0 else 0)
        for k in range(13):
            val=mixed(k,0);assert val.is_Integer and val>=0
            parity=0 if k%2 else (u*Q**(k//2)*s.Matrix([1,0]))[0]%2
            assert val%2==parity
        for i in range(13):
            for j in range(7):
                if i+2*j>12:continue
                val=mixed(i,j);assert val.is_Integer and val>=0
                if i%2!=j%2:assert val%2==0
        assert mixed(0,4)>=63-16*t+t*t
        actual[t]+=n
        for j,v in enumerate([tau,R,delta]):totals[j]+=n*v
        mass+=n*w
    expected=s.Matrix(multiplicities)
    for lo,hi,d in pairs:expected[hi]=0
    assert actual==census and totals==[87,274,18] and mass==expected
    print(name+': PASS exact local moments0..12, C parity, mixed C/D nonnegative integers through weighted degree12, and global census/multiplicities')
print('Monic degree13 annihilator plus integral initial13 moments proves all later C moments integral. No all-degree positivity/parity or graph realization claim.')
