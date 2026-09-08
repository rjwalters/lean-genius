"""Repair one rational rank-one projector; no full spectral realization."""
import contextlib
from fractions import Fraction as F
from itertools import product
import io
from math import isqrt
from pathlib import Path
import runpy

with contextlib.redirect_stdout(io.StringIO()):
    v=runpy.run_path(str(Path(__file__).with_name('verify_q1024_local_walk_control.py')))
q,n=v['q'],v['n']
supports,basis,solve=v['supports'],v['basis'],v['solve']
def old_weight(vertex):
    _,d,a5=v['parents'][0 if vertex<96 else 1 if vertex<8168 else 2]
    w,z,_=v['local'](d,a5,[int(vertex<c) for c in v['ceil_counts']])
    return (w[2]+z[2]/4)/2
ratio=old_weight(32256)/old_weight(0)
assert ratio==F(93649,93652)
assert isqrt(ratio.numerator)**2!=ratio.numerator
print('Original nine-type measures fail rational rank-one square ratio PASS')

def p(y):return (y-4)*(y-8)*v['g'](y)
alpha=F((q+4)*p(q*q),n)
beta=8*p(16)
assert alpha.denominator==1 and alpha%2==0 and F(beta,n)==-749385
assert (alpha+F(beta,n))%2==1
rhos=[F(50,61),F(72,61)]
assert sum(rhos)==2

def local(d,a5,bits,rho):
    r=[f+2*b for f,b in zip(v['floors'],bits)]
    K=alpha+rho*beta/n
    assert K.denominator==1 and K%2==0
    r.append(K+12*r[4]-32*r[3]-4*(r[2]-12*r[1]+32*r[0]))
    ev=[F(1),F(q),F(q*(2*q-1))]+r[:3]
    od=[F(0),F(q-d),F(a5)]+r[3:]
    w=solve([x-F(basis(q*q)[i],n) for i,x in enumerate(ev)])
    z=solve([x-F(q*basis(q*q)[i],n) for i,x in enumerate(od)])
    assert all(x>=0 and y*y<=a*x*x for a,x,y in zip(supports,w,z))
    assert (w[2]+z[2]/4)/2==rho/n
    moments=[F(q**k,n)+sum(x*a**(k//2) if k%2==0 else y*a**((k-1)//2)
             for a,x,y in zip(supports,w,z)) for k in range(14)]
    assert moments[:6]==[1,0,q,q-d,q*(2*q-1),a5]
    assert all(x.denominator==1 and x%2==0 for x in moments[1:])
    d3=q**4+q**3-3*q+2-moments[6]
    assert d3%2==0 and 0<=d3<=(q-1)*(q-2)
    assert sum(c*x for c,x in zip(v['h'],moments))==F(v['v']['evaluate'](v['h'],q),n)
    return w,z

for _,d,a5 in v['parents']:
    for rho in rhos:
        for bits in product((0,1),repeat=5):local(d,a5,bits,rho)
print('All192 constrained choices: positivity, fixed rank-one weights and local integrality PASS')

boundaries=sorted(set([0,96,8168,n//2,n]+[int(x) for x in v['ceil_counts'][:5]]))
sum_w=[F(0)]*6;sum_z=[F(0)]*6
norm2=0;populations=[]
for lo,hi in zip(boundaries,boundaries[1:]):
    count=hi-lo
    assert count>0 and count%2==0
    _,d,a5=v['parents'][0 if lo<96 else 1 if lo<8168 else 2]
    magnitude=5 if lo<n//2 else 6
    rho=rhos[int(lo>=n//2)]
    w,z=local(d,a5,[int(lo<c) for c in v['ceil_counts'][:5]],rho)
    sum_w=[x+count*y for x,y in zip(sum_w,w)]
    sum_z=[x+count*y for x,y in zip(sum_z,z)]
    norm2+=count*magnitude**2
    populations.append((count,magnitude))
assert sum_w==[n*x for x in v['W']] and sum_z==[n*x for x in v['Z']]
assert norm2==61*n//2
# In each even-sized type, use equally many positive and negative entries.
# Thus x^T 1=0, x^T x=norm2, and xx^T/norm2 is a rational rank-one
# projector orthogonal to J/n, with precisely the asserted diagonals.
assert all(F(magnitude**2,norm2)==rho/n for magnitude,rho in zip([5,6],rhos))
print('Nine even populations:',populations)
print('Exact aggregate spectrum and two orthogonal rational rank-one projectors PASS')
print('Remaining projectors and integer adjacency realization are not constructed.')
