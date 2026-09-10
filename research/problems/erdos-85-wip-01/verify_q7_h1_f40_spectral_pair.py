import json,functools
from pathlib import Path
import sympy as s
x=s.symbols('x');base=Path(__file__).parent
fdata={'factors': [{'coefficients': [1, -3], 'multiplicity': 1}, {'coefficients': [1, 0], 'multiplicity': 2}, {'coefficients': [1, 1], 'multiplicity': 2}, {'coefficients': [1, -1, -4], 'multiplicity': 1}, {'coefficients': [1, 0, -8], 'multiplicity': 1}, {'coefficients': [1, 0, -7], 'multiplicity': 5}, {'coefficients': [1, 0, -6], 'multiplicity': 3}, {'coefficients': [1, 0, -5], 'multiplicity': 1}, {'coefficients': [1, 0, -3], 'multiplicity': 1}, {'coefficients': [1, 1, -5], 'multiplicity': 2}, {'coefficients': [1, 2, -2], 'multiplicity': 3}]}
cdata={'factors': [{'coefficients': [1, 3], 'multiplicity': 1}, {'coefficients': [1, 1], 'multiplicity': 1}, {'coefficients': [1, -2, -4], 'multiplicity': 2}, {'coefficients': [1, 0, -8], 'multiplicity': 3}, {'coefficients': [1, 0, -7], 'multiplicity': 3}, {'coefficients': [1, 0, -6], 'multiplicity': 6}, {'coefficients': [1, 0, -5], 'multiplicity': 2}, {'coefficients': [1, 1, -7], 'multiplicity': 1}, {'coefficients': [1, 1, -5], 'multiplicity': 4}, {'coefficients': [1, 2, -1], 'multiplicity': 1}]}
def roots(data):
 out=[]
 for f in data['factors']:
  for r in s.solve(s.Poly.from_list(f['coefficients'],x).as_expr(),x):out.extend([r]*f['multiplicity'])
 def cmp(a,b):
  diff=s.simplify(a-b)
  if diff==0:return 0
  return -1 if bool(diff<0) else 1
 return sorted(out,key=functools.cmp_to_key(cmp))
a=roots(cdata);b=roots(fdata)
assert len(a)==46 and len(b)==39
assert all(bool(a[i]<=b[i]) and bool(b[i]<=a[i+7]) for i in range(39))
mom=[int(s.simplify(sum(r**k for r in b))) for k in range(5)]
assert mom==[39,-6,204,-54,1344]
rho=s.Poly(1,x)
for f in fdata['factors']:rho*=s.Poly.from_list(f['coefficients'],x)**f['multiplicity']
assert int(rho.eval(6))%80==0

def mul(a,b,N=None):
 n=len(a)+len(b)-1
 if N is not None:n=min(n,N+1)
 out=[0]*n
 for i,v in enumerate(a):
  for j,w in enumerate(b):
   if i+j<n:out[i+j]+=v*w
 return out
bass=[1,-6,5]
for f in fdata['factors']:
 c=f['coefficients'];p=[1,c[1],5] if len(c)==2 else [1,c[1],10+c[2],5*c[1],25]
 for _ in range(f['multiplicity']):bass=mul(bass,p)
assert all(bass[i]%2==0 for i in range(1,len(bass),2))
root=[bass[2*i]%2 for i in range((len(bass)+1)//2)];square=mul(root,root)
assert all((v-(square[i] if i<len(square) else 0))%4==0 for i,v in enumerate(bass))
N=20;full=bass[:N+1]
for _ in range(80):full=mul(full,[1,0,-1],N)
tr=[0]*(N+1);cy=[0]*(N+1)
for k in range(1,N+1):
 tr[k]=-k*full[k]-sum(full[j]*tr[k-j] for j in range(1,k))
 v=tr[k]-sum(j*cy[j] for j in range(1,k) if k%j==0)
 assert v%k==0;cy[k]=v//k
 assert cy[k]>=0 and cy[k]%2==0
assert cy[1:5]==[0,0,54,0]
out={'scope':'Exact pair of spectral polynomials only, no simultaneous matrix or graph realization','T_N':16,'T_F':27,'rho_factors':fdata['factors'],'rho_coefficients':list(map(int,rho.all_coeffs())),'rho_moments0_to4':mom,'exact_rank7_interlacing':True,'Hoffman_mod80':True,'full_F_Bass_mod4_square':True,'F_primitive_oriented_counts_through20':cy[1:]}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n');print('PASS: exact rank7 interlacing, F40 moments, Hoffman80, full Bass mod4, primitive counts20; spectral pair only')
