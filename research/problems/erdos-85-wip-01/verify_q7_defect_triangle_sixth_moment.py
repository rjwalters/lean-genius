"""Exact defect-triangle identity and explicit H3 scalar-relaxation checks."""
import json,math
from pathlib import Path
import sympy as s
x,h=s.symbols('x h')
# Quotient eigenvalues a,b satisfy a+b=7,ab=h. D has a-1,b-1,
# h-1 copies of -1, and residual eigenvalues 6-lambda^2.
constant=s.expand(216*(48-2*h)-108*(294-13*h)+18*(2058-97*h)
                  +125-15*(h-6)-(h-1))
assert constant==15876-790*h
bad=[([1,-2],8),([1,2],2),([1,3],6),([1,-1,-7],3),([1,0,-6],4),([1,0,-5],2),([1,1,-7],2),([1,1,-4],2)]
good=[([1,-3],4),([1,2],4),([1,-1,-7],1),([1,0,-6],4),([1,1,-7],2),([1,1,-5],10)]

def polynomial(fs):
 p=s.Poly(1,x)
 for c,m in fs:p*=s.Poly.from_list(c,x)**m
 return p

def moments(p,N):
 c=list(map(int,p.all_coeffs()));v=[p.degree()]
 for k in range(1,N+1):
  v.append(-sum(c[j]*v[k-j] for j in range(1,min(k,p.degree()+1)))
           -(k*c[k] if k<=p.degree() else 0))
 return v

def mul(a,b,N=None):
 n=len(a)+len(b)-1
 if N is not None:n=min(n,N+1)
 c=[0]*n
 for i,v in enumerate(a):
  for j,w in enumerate(b):
   if i+j<n:c[i+j]+=v*w
 return c

def reduced_bass(fs):
 r=[1,-7,12,-45,81,-294,252]
 for c,m in fs:
  f=[1,c[1],6] if len(c)==2 else [1,c[1],12+c[2],6*c[1],36]
  for _ in range(m):r=mul(r,f)
 return r

def check_old(fs,T,R):
 p=polynomial(fs);v=moments(p,24)
 assert v[:5]==[42,-7,255,6*T-280,1767]
 assert v[5]+3309-72*T==R
 lower=(7-s.sqrt(37))/2;upper=(17+s.sqrt(37))/2
 for c,_ in fs:
  assert all(bool(z*z>lower) and bool(z*z<upper) for z in s.solve(s.Poly.from_list(c,x).as_expr(),x))
 assert p.eval(18)%67==0 and p.eval(0)%49==0
 assert s.Poly(p.as_expr(),x,modulus=7).nth(0)==0
 assert s.Poly(p.as_expr(),x,modulus=7).nth(1)==0
 bass=reduced_bass(fs);root=[bass[2*i]%2 for i in range((len(bass)+1)//2)];sq=mul(root,root)
 assert all((v-(sq[i] if i<len(sq) else 0))%4==0 for i,v in enumerate(bass))
 return p,v,bass

bp,bv,_=check_old(bad,27,178)
assert bv[6]==13686 and 13506-bv[6]==-180
p,v,bass=check_old(good,29,274)
assert v[1:7]==[-7,255,-106,1767,-947,13470]
assert 13506-v[6]==36
assert 0<=274<=min(352,348) and 274%2==0 and (274-3*29-7)%5==0
# All mixed traces through exponents 8,8: C and D commute, are nonnegative.
q=[2,7]
for k in range(2,25):q.append(7*q[-1]-3*q[-2])
table=[]
for i in range(9):
 row=[]
 for j in range(9):
  z=sum(math.comb(j,k)*6**(j-k)*(-1)**k*v[i+2*k] for k in range(j+1))
  z+=sum(math.comb(j,k)*(-1)**(j-k)*q[i+k] for k in range(j+1))
  if i==0:z+=2*(-1)**j
  assert z>=0;row.append(z)
 table.append(row)
assert table[0][1:5]==[0,252,36,2976]
# Actual full A Bass factors include the paired high factor squared and m-n=124.
N=20;full=bass[:N+1]
for _ in range(2):full=mul(full,[1,0,6,0,42],N)
for _ in range(124):full=mul(full,[1,0,-1],N)
tr=[0]*(N+1);cy=[0]*(N+1)
for k in range(1,N+1):
 tr[k]=-k*full[k]-sum(full[j]*tr[k-j] for j in range(1,k))
 z=tr[k]-sum(j*cy[j] for j in range(1,k) if k%j==0)
 assert z%k==0;cy[k]=z//k
 assert cy[k]>=0 and cy[k]%2==0
assert cy[1:5]==[0,0,82,0]
out={'scope':'Paper identity plus exact scalar polynomial checks; no simultaneous integer C/D or graph realization',
     'defect_third_trace':'15876-790*h-p6(psi_h)',
     'rejected_H3_factors':bad,'rejected_p6':bv[6],'rejected_defect_third_trace':-180,
     'H3_factors':good,'H3_psi_coefficients':list(map(int,p.all_coeffs())),
     'H3_moments1_to6':v[1:7],'T':29,'mixed_fifth_R':274,'pair_R_upper':352,'triple_R_upper':348,
     'defect_triangle_count':6,'mixed_trace_table_i_j_0_to8':table,
     'full_A_primitive_oriented_counts_through20':cy[1:]}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS: general sixth-moment identity; first H3 polynomial rejected; second passes listed exact scalar tests, not a graph')
