"""Exact nine-type local spectral control; no graph realization.

Uses SymPy only for a six-by-six rational inverse. The finite recurrence
argument for all lengths is in Q1024_LOCAL_WALK_CONTROL.md.
"""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import runpy
import sympy as sp

v = runpy.run_path(str(Path(__file__).with_name('verify_unbounded_spectral_filter_control.py')))
q, t = 1024, 32
n = q*q
Q, C, S, R = v['configuration'](1)
pairs = {v['evaluate'](a,t):v['evaluate'](c,t) for a,c in zip(S,C)}
supports = [4,8,16,q-t,q,q+t]
W = [F(2*pairs[4]+2,n),F(2*pairs[8],n),F(q//4+1,n)] + [F(2*pairs[a],n) for a in supports[3:]]
Z = [F(-4,n),F(0),F(-q+4,n),F(0),F(0),F(0)]
def g(y): return (y-(q-t))*(y-q)*(y-(q+t))
def basis(y): return [1,y,y*y,g(y),y*g(y),y*y*g(y)]
# h(X)=product(X^2-a) is the monic residual annihilator. Its constant
# term and principal quotient are even, the finite integrality certificate.
h=[1]
for a in supports: h=v['mul'](h,[-a,0,1])
assert h[-1]==1 and h[0]%2==0
assert v['evaluate'](h,q)%(2*n)==0
full=v['add'](v['scale'](h,-q),[0]+h)
assert len(full)==14 and full[-1]==1 and full[0]%2==0
assert max(supports)<33**2 and q**5>n*33**5
B = sp.Matrix([basis(a) for a in supports]).T.inv()
def solve(values):
    return [F(x) for x in B*sp.Matrix(values)]
def mean(k):
    return F(v['evaluate'](v['symbolic_moment'](k,C,S,R),t),n)
base_even = [F(basis(q*q)[i],n)+sum(basis(a)[i]*w for a,w in zip(supports,W)) for i in range(3,6)]
base_odd = [F(q*basis(q*q)[i],n)+sum(basis(a)[i]*z for a,z in zip(supports,Z)) for i in range(3,6)]
means = base_even+base_odd
floors = [2*(x//2) for x in means]
ceil_counts = [n*(x-f)/2 for x,f in zip(means,floors)]
assert all(c.denominator==1 and 0<=c<n for c in ceil_counts)
parents = [(96,2,q**3-30),(8072,2,q**3-32),(n-8168,0,q**3)]
def local(d,a5,bits):
    rounded = [f+2*b for f,b in zip(floors,bits)]
    ev = [F(1),F(q),F(q*(2*q-1))]+rounded[:3]
    od = [F(0),F(q-d),F(a5)]+rounded[3:]
    w = solve([x-F(basis(q*q)[i],n) for i,x in enumerate(ev)])
    z = solve([x-F(q*basis(q*q)[i],n) for i,x in enumerate(od)])
    assert all(x>=0 and y*y<=a*x*x for a,x,y in zip(supports,w,z)), (d,a5,bits)
    def moment(k):
        return F(q**k,n)+sum((x*a**(k//2) if k%2==0 else y*a**((k-1)//2)) for a,x,y in zip(supports,w,z))
    m=[moment(k) for k in range(14)]
    assert m[:5]==[1,0,q,q-d,q*(2*q-1)] and m[5]==a5
    assert all(x.denominator==1 and x%2==0 for x in m[1:])
    assert sum(c*x for c,x in zip(h,m))==F(v['evaluate'](h,q),n)
    # Existing pointwise sixth-moment constraint is also retained.
    d3=q**4+q**3-3*q+2-m[6]
    assert 0<=d3<=(q-1)*(q-2) and d3%2==0
    return w,z,m

for _,d,a5 in parents:
    for bits in product((0,1),repeat=6): local(d,a5,bits)
print('All 192 floor/ceil choices: nonnegative weights and even integral moments1..13 PASS')
boundaries=sorted(set([0,96,8168,n]+[int(x) for x in ceil_counts]))
sum_w=[F(0)]*6;sum_z=[F(0)]*6
types=[]
for lo,hi in zip(boundaries,boundaries[1:]):
    _,d,a5=parents[0 if lo<96 else 1 if lo<8168 else 2]
    bits=[int(lo<c) for c in ceil_counts]
    w,z,m=local(d,a5,bits)
    count=hi-lo
    sum_w=[x+count*y for x,y in zip(sum_w,w)]
    sum_z=[x+count*y for x,y in zip(sum_z,z)]
    types.append((count,d,a5,m[6]))
assert sum_w==[n*x for x in W] and sum_z==[n*x for x in Z]
print('Integer vertex counts and exact aggregate eigenvalue weights PASS')
print('Monic degree13 recurrence with even constant: all-length integrality certificate PASS')
print('ceil counts:',ceil_counts)
print('types (count,d,A5,A6):',types)
print('No graph, off-diagonal projectors, or integer matrix has been constructed.')
