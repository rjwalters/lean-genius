"""Exact fixed-polynomial local measures; no optimization or graph assertion."""
from fractions import Fraction as F
import json
from math import comb, isqrt
from pathlib import Path
import sympy as s

base=Path(__file__).parent
w=json.loads((base/'q7_h5_local_galois_measures.json').read_text())
assert w['checked_integer_diagonal_degree']==10
assert (w['h'],w['T'],w['R'],w['defect_triangles'])==(5,19,16,3)
factors=[([1,-3],2),([1,3],2),([1,0,-6],8),([1,0,-3],2),([1,1,-7],4),([1,1,-4],2),([1,1,-3],1)]
columns=[];multiplicities=[];position=0
for cs,mult in factors:
 if len(cs)==2:
  desc=w['columns'][position];position+=1
  assert desc=={'factor':cs,'sign':0}
  columns.append([F(-cs[1])**k for k in range(11)]);multiplicities.append(mult)
 else:
  b,c=cs[1:];disc=b*b-4*c
  sums=[F(2),F(-b)];diff=[F(0),F(1)]
  for k in range(2,11):
   sums.append(-b*sums[-1]-c*sums[-2]);diff.append(-b*diff[-1]-c*diff[-2])
  pair_r=[]
  for sign in [-1,1]:
   desc=w['columns'][position];position+=1
   assert desc['factor']==cs and desc['sign']==sign
   r=F(desc['r']);assert 0<r*r<disc;pair_r.append(r)
   columns.append([(sums[k]+sign*r*diff[k])/2 for k in range(11)])
   multiplicities.append(mult)
  assert pair_r[0]==pair_r[1]
assert position==len(w['columns'])==12
Q=s.Matrix([[7,5],[-1,0]]);gram=s.Matrix([[44,40],[40,60]])
assert w['checked_mixed_weighted_degree']==10
seen=set()
for profile in w['results']:
 n3=profile['n3'];assert n3 in range(3) and n3 not in seen;seen.add(n3)
 census=[0]*4;totals=[0]*3;mass=[F(0)]*12;norms=[]
 for group in profile['groups']:
  t,tau,R,delta,count=[group[k] for k in ['t','tau','R','delta','count']]
  assert all(type(v) is int for v in [t,tau,R,delta,count])
  assert 0<=t<=3 and int(t==0)<=tau<=3-t and count>0
  survivors=t+2*tau-1
  assert R%2==0 and 0<=R<=2*[0,0,1,3,4,6][survivors]
  assert 0<=delta<=(6-t)*(5-t)//2
  v=s.Matrix([[1,t]])
  q=[F((v*Q**k*gram.inv()*v.T)[0]) for k in range(11)]
  z=F(t*(5-t),35)
  target=[1-q[0]-z,-q[1],7-t-q[2],2*tau-q[3],(7-t)*(13-t)-5-q[4]]
  target.append(R+12*target[3]-36*target[1]-q[3]+2*q[2]-q[1])
  target.append(216*target[0]-108*target[2]+18*target[4]+q[3]-3*q[2]+3*q[1]-q[0]-z-2*delta)
  weights=list(map(F,group['cone_weights']))
  assert len(weights)==12 and all(v>=0 for v in weights)
  moments=[sum(a*col[k] for a,col in zip(weights,columns)) for k in range(11)]
  assert moments[:7]==[count*v for v in target]
  for k in range(11):
   full= moments[k]/count + q[k] + (z if k==0 else 0)
   assert full.denominator==1 and full>=0
   if k>0:
    parity=0 if k%2 else int((v*Q**(k//2)*s.Matrix([1,0]))[0])%2
    assert full.numerator%2==parity
  residual=[a/count for a in moments]
  for j in range(6):
   for i in range(11-2*j):
    mixed=sum(comb(j,k)*6**(j-k)*(-1)**k*residual[i+2*k] for k in range(j+1))
    mixed+=F((v*Q**i*(Q-s.eye(2))**j*gram.inv()*v.T)[0])
    if i==0:mixed+=(-1)**j*z
    assert mixed.denominator==1 and mixed>=0
    if i%2!=j%2:assert mixed.numerator%2==0
    if (i,j)==(0,4):assert mixed>=61-16*t+t*t
  # Simple x²+x-3 factor: necessary norm-square ratios for rank-one projectors.
  u0,u1=weights[-2:];rho=F(w['columns'][-1]['r'])
  A=(u0+u1)/(2*count);B=rho*(u1-u0)/(26*count)
  norm=A*A-13*B*B
  if norm:norms.append(norm)
  census[t]+=count
  totals=[a+count*b for a,b in zip(totals,[tau,R,delta])]
  mass=[a+b for a,b in zip(mass,weights)]
 assert census==[14-n3,20+3*n3,10-3*n3,n3]
 assert totals==[3*w['T'],w['R'],3*w['defect_triangles']]
 assert mass==multiplicities
 assert norms
 ratios=[n/norms[0] for n in norms[1:]]
 assert any(isqrt(a.numerator)**2!=a.numerator or isqrt(a.denominator)**2!=a.denominator for a in ratios)
 print('PASS exact H5 profile',n3,': local moments0..6, conjugate nonnegative weights, integer census, global multiplicities, per-vertex C parity and mixed nonnegative integers through weighted degree10; saved weights fail simple-projector norm-square test')
assert seen=={0,1,2}
print('No joint symmetric operator, off-diagonal projector, lattice realization, or graph is constructed.')
