#!/usr/bin/env python3
"""Weighted-projector parity controls; no q7 graph/spectrum search."""
import itertools
import json
import random

import sympy as sp

x,a = sp.symbols('x a')


def reduce_field(expr,h):
    return sp.rem(sp.cancel(expr),a*a-7*a+h,a)


def zero_mod(expr,modulus):
    coefficients=sp.Poly(sp.expand(expr),a,x).coeffs()
    assert all(c.is_Integer for c in coefficients)
    return all(int(c)%modulus==0 for c in coefficients)


def binary_residual_root(psi):
    quotient,remainder=sp.div(sp.Poly(psi,x,modulus=2),sp.Poly(x*x+x+1,x,modulus=2))
    assert remainder.is_zero
    assert all(int(quotient.nth(i))%2==0 for i in range(1,quotient.degree()+1,2))
    return sum((int(quotient.nth(2*i))%2)*x**i for i in range(quotient.degree()//2+1))


def graph_control(seed):
    rng=random.Random(seed)
    C=sp.zeros(24)
    for j in range(4):
        C[j,(j+1)%4]=C[(j+1)%4,j]=1
        for color in range(5):
            v=4+4*color+j
            C[j,v]=C[v,j]=1
    for color in range(5):
        matching=rng.choice([[1,0,3,2],[2,3,0,1],[3,2,1,0]])
        for j,w in enumerate(matching):
            C[4+4*color+j,4+4*color+w]=1
        for other in range(color):
            perm=list(range(4));rng.shuffle(perm)
            for j,w in enumerate(perm):
                v1,v2=4+4*color+j,4+4*other+w
                C[v1,v2]=C[v2,v1]=1
    assert C==C.T and all(C[i,i]==0 for i in range(24))
    assert all(c in (0,1) for c in C)
    c4=[0,1,2,3]
    assert len(set(c4))==4 and all(C[c4[i],c4[(i+1)%4]]==1 for i in range(4))
    one=sp.ones(24,1);t=sp.Matrix([0]*4+[1]*20)
    assert C*one==7*one-t and C*t==5*one
    B=sp.zeros(5,24)
    for color,j in itertools.product(range(5),range(4)):
        B[color,4+4*color+j]=1
    assert B*C==sp.ones(5,24)
    seen={0}
    while True:
        larger=seen|{j for i in seen for j in range(24) if C[i,j]}
        if larger==seen:break
        seen=larger
    assert len(seen)==24
    chi=C.charpoly(x).as_expr()
    psi,remainder=sp.div(chi,x**4*(x*x-7*x+5),x)
    assert remainder==0
    S=binary_residual_root(psi)
    tau=reduce_field(a**4*reduce_field(psi.subs(x,a),5)*
                     sp.invert(24*a-20,a*a-7*a+5,a),5)
    assert all(c.is_Integer for c in sp.Poly(tau,a).all_coeffs())
    rhs=reduce_field(a*(7-a)**2*S.subs(x,7-a),5)
    assert zero_mod(tau-rhs,2)
    assert not zero_mod(tau,2)  # Nontrivial parity calibration.
    return {'seed':seed,'order':24,'residual_degree':sp.degree(psi,x),
            'tau':str(tau),'tau_mod2':str(sp.Poly(tau,a,modulus=2).as_expr()),
            'explicit_C4_vertices':c4,
            'scope':'Actual C with degree/support identities; contains C4 and is not a q7 candidate'}


def coefficient_controls(T):
    q=x*x+x+1
    S=x**18+x**17+x**16+(T%2)*x**15+(1-T%2)*x**14+1
    base=sp.Poly(q*S*S,x)
    coeff=[int(base.nth(i)) for i in range(39)]
    leading={37:7,36:-90,35:-665-2*T,34:4012-14*T}
    for i,target in leading.items():
        assert (target-coeff[i])%4==0
        coeff[i]=target
    coeff[0]=2401*(coeff[0]%4)
    for i in range(1,4):
        coeff[i]=7*((3*coeff[i])%4)  # Preserve mod4, force mod7 zero.
    psi=sum(c*x**i for i,c in enumerate(coeff))
    error=int(psi.subs(x,8))%13
    coeff[4]+=4*((-error*pow(4*pow(8,4,13),-1,13))%13)
    psi=sum(c*x**i for i,c in enumerate(coeff))
    results=[]
    for bit0,bit1 in itertools.product((0,1),repeat=2):
        candidate=sp.expand(psi+4*13*2401*bit0+4*13*7*bit1*x)
        P=sp.Poly(candidate,x)
        assert all(P.nth(i)==target for i,target in leading.items())
        assert zero_mod(candidate-q*S*S,4)
        assert int(candidate.subs(x,8))%13==0
        assert all(int(P.nth(i))%7==0 for i in range(4))
        assert P.nth(0)!=0 and int(P.nth(0))%2401==0
        assert binary_residual_root(candidate)==S
        error=reduce_field(candidate.subs(x,a)-4*(7-a)*S.subs(x,7-a),5)
        passes=zero_mod(error,8)
        results.append({'bits':[bit0,bit1],'weighted_mod8_pass':passes,
            'error_coefficients_mod8':[int(sp.Poly(error,a).nth(i))%8 for i in range(2)],
            'coefficients_ascending':[int(P.nth(i)) for i in range(39)]})
    assert sum(row['weighted_mod8_pass'] for row in results)==1
    return {'T':T,'scope':'Coefficient consistency only; no real-root/spectral/graph assertion',
            'controls':results}


def main():
    # Exact denominator reductions used to specialize the universal tau parity.
    for h,power,expected in [(1,3,a),(3,1,7-a),(5,2,7-a),(7,1,7-a)]:
        eta=((49-h)*a-8*h)/(2**power)
        assert all(c.is_Integer for c in sp.Poly(eta,a).all_coeffs())
        inverse=sp.invert(a**(h-1),a*a-7*a+h,a)
        multiplier=reduce_field(eta*a*(7-a)**((h-1)//2)*inverse,h)
        # a is odd-norm; rational odd denominators are units modulo2.
        num,den=sp.fraction(sp.together(multiplier-expected))
        assert int(den)%2==1 and zero_mod(num,2)
    # H7 Ihara polynomial implies the weighted condition for any binary S;
    # check the field factor and Frobenius separately, not random spectra.
    assert zero_mod(reduce_field(a*a+3*a+1-2*(7-a),7),4)
    assert zero_mod(reduce_field(a*a-(7-a),7),2)
    result={'scope':'Exact algebra, three non-q7 graph controls and eight coefficient controls',
            'graph_controls':[graph_control(i) for i in range(3)],
            'coefficient_controls':[coefficient_controls(T) for T in (5,6)]}
    print(json.dumps(result,indent=2,default=int))


if __name__=='__main__':
    main()
