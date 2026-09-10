"""Exact rational local moments at conjugate eigenvalues; no graph assertion."""
from fractions import Fraction as F
from pathlib import Path
from math import comb
import json

base=Path(__file__).parent
w=json.loads((base/'q7_h7_galois_local_measure.json').read_text())
control=next(p for p in json.loads((base/'q7_h5_h7_integer_spectral_controls.json').read_text())['controls'] if p['h']==7)
assert w['h']==7 and (w['T'],w['R'],w['defect_triangles'])==(13,30,26)
assert [([1,c['b'],c['c']],c['multiplicity']) for c in w['cones']]==[(c,m) for c,m in control['factors']]
columns=[]
for factor in w['cones']:
 b,c,r=factor['b'],factor['c'],F(factor['r'])
 disc=b*b-4*c
 assert disc==factor['disc'] and 0<r and r*r<disc
 q,d=[2,-b],[0,1]
 for k in range(2,7):
  q.append(-b*q[-1]-c*q[-2]);d.append(-b*d[-1]-c*d[-2])
 columns.extend([[(q[k]+sign*r*d[k])/2 for k in range(7)] for sign in (1,-1)])

def multiply(A,B):
 return [[sum(A[i][k]*B[k][j] for k in range(2)) for j in range(2)] for i in range(2)]

def quadratic_form(row,M):
 return sum(row[i]*M[i][j]*row[j] for i in range(2) for j in range(2))

A=[[F(7),F(7)],[-F(1),F(0)]]
Ginv=[[F(98,980),-F(56,980)],[-F(56,980),F(42,980)]]
fixed=[]
for t in range(3):
 power=[[F(1),F(0)],[F(0),F(1)]];q=[]
 for k in range(7):
  q.append(quadratic_form([1,t],multiply(power,Ginv)));power=multiply(power,A)
 fixed.append(q)
ex=[0,0,1,3,4,6];census=[0,0,0];totals=[F(0)]*14;incidence=overlap=defect_incidence=0;seen=set()
for group in w['groups']:
 t,tau,R,delta,n=[group[k] for k in ['t','tau','R','delta','count']]
 assert all(isinstance(v,int) for v in [t,tau,R,delta,n]) and n>0
 assert (t,tau,R,delta) not in seen;seen.add((t,tau,R,delta))
 assert 0<=t<=2 and int(t==0)<=tau<=3-t
 assert 0<=R<=2*ex[t+2*tau-1] and R%2==0
 assert 0<=delta<=comb(6-t,2)
 weights=list(map(F,group['cone_weights']))
 assert len(weights)==14 and all(v>=0 for v in weights)
 for i,factor in enumerate(w['cones']):
  u=weights[2*i]+weights[2*i+1];v=F(factor['r'])*(weights[2*i]-weights[2*i+1])
  assert (u==v==0) or (u>0 and v*v<factor['disc']*u*u)
 moments=[sum(weights[j]*columns[j][k] for j in range(14)) for k in range(7)]
 q=fixed[t];z=F(t*(7-t),49)
 m0=1-q[0]-z;m1=-q[1];m2=7-t-q[2];m3=2*tau-q[3];m4=(7-t)*(13-t)-7-q[4]
 m5=R+12*m3-36*m1-q[3]+2*q[2]-q[1]
 m6=216*m0-108*m2+18*m4+q[3]-3*q[2]+3*q[1]-q[0]-z-2*delta
 assert moments==[n*v for v in [m0,m1,m2,m3,m4,m5,m6]]
 # The full C local moments through six are integral and nonnegative.
 full=[F(1)]+[moments[k]/n+q[k] for k in range(1,7)]
 assert all(v.denominator==1 and v>=0 for v in full)
 assert all(full[k]%2==0 for k in [1,3,5])
 census[t]+=n;incidence+=n*tau;overlap+=n*R;defect_incidence+=n*delta
 totals=[a+b for a,b in zip(totals,weights)]
assert census==[7,14,21] and (incidence,overlap,defect_incidence)==(39,30,78)
assert totals==[F(f['multiplicity']) for f in w['cones'] for _ in range(2)]
assert [sum(totals[j]*columns[j][k] for j in range(14)) for k in range(7)]==control['residual_power_sums_0_to6']
print('PASS: exact Galois-compatible local moments0..6, integer local types, positive conjugate weights, and global spectral multiplicities; no common matrix or graph')
