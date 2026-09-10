"""Verify an explicit spectral relaxation, without any optimization dependency."""
import json
from pathlib import Path
import sympy as s
x=s.symbols("x")
factors=[([1,3],1),([1,1],1),([1,-2,-4],2),([1,0,-8],3),([1,0,-7],3),([1,0,-6],6),([1,0,-5],2),([1,1,-7],1),([1,1,-5],4),([1,2,-1],1)]
psi=s.Poly(1,x);mom=[s.Integer(0)]*5;lower=(7-s.sqrt(45))/2;upper=(17+s.sqrt(45))/2
for coeff,m in factors:
 f=s.Poly.from_list(coeff,x);psi*=f**m
 roots=s.solve(f.as_expr(),x)
 assert len(roots)==f.degree()
 assert all(bool(r*r>lower) and bool(r*r<upper) for r in roots)
 for j in range(5):mom[j]+=m*sum(r**(j+1) for r in roots)
mom=[int(s.simplify(v)) for v in mom]
assert psi.degree()==46 and mom==[-7,281,-64,1961,-507]
T=(mom[2]+322)//6;assert T==43 and 18<=T<=45
mixed_fifth=mom[4]+3847-72*T
assert mixed_fifth==244 and mixed_fifth<=18*T-264
assert int(psi.eval(1))%5==0
q=s.Poly(x*x+x+1,x);assert all(int(v)%16==0 for v in psi.rem(q).all_coeffs())
def mul(a,b,limit=None):
 n=len(a)+len(b)-1
 if limit is not None:n=min(n,limit+1)
 c=[0]*n
 for i,v in enumerate(a):
  for j,w in enumerate(b):
   if i+j<n:c[i+j]+=v*w
 return c
H=[1,-7,12,-43,79,-294,252]
reduced=mul([1,0,-1],H)
R=[1]
for c,m in factors:
 f=[1,c[1],6] if len(c)==2 else [1,c[1],12+c[2],6*c[1],36]
 for _ in range(m):R=mul(R,f)
reduced=mul(reduced,R)
assert all(reduced[i]%2==0 for i in range(1,len(reduced),2))
root=[reduced[2*i]%2 for i in range((len(reduced)+1)//2)]
square=mul(root,root)
assert all((v-(square[i] if i<len(square) else 0))%4==0 for i,v in enumerate(reduced))
N=20;full=mul(H,R,N)
for _ in range(123):full=mul(full,[1,0,-1],N)
tr=[0]*(N+1);cycles=[0]*(N+1)
for k in range(1,N+1):
 tr[k]=-k*full[k]-sum(full[j]*tr[k-j] for j in range(1,k))
 v=tr[k]-sum(j*cycles[j] for j in range(1,k) if k%j==0)
 assert v%k==0;cycles[k]=v//k
 assert cycles[k]>=0 and cycles[k]%2==0
assert cycles[1:5]==[0,0,94,0]
result=dict(scope="Verified spectral relaxation only; no adjacency matrix, joint C/D representation, graph, or completeness claim",factors=[dict(coefficients=c,multiplicity=m) for c,m in factors],degree=46,moments=mom,all_low_triangles=T,mixed_fifth_R=mixed_fifth,mixed_fifth_upper_bound=18*T-264,strict_root_window=True,ihara_mod4_square=True,cyclotomic_mod16=True,overlap_mod5=True,oriented_primitive_counts_through20=cycles[1:],psi_coefficients=list(map(int,psi.all_coeffs())))
Path(__file__).with_suffix(".json").write_text(json.dumps(result,indent=2)+"\n")
print("PASS: exact roots/moments, Ihara mod4, H1 mod16, mod5 overlap, nonnegative even primitive counts through20; spectral relaxation only")
