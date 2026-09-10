"""Integral incidence-lattice controls for necessary residual congruences."""
import json
from itertools import combinations
from pathlib import Path
import sympy as s
rows=[]
for h,triple,prime,alpha,beta,lam in [(1,0,5,1,-6,1),(3,0,67,12,-23,18),(3,1,67,12,-23,18)]:
 supports=[]
 if h==1: supports=[()]*40+[(0,)]*8
 else:
  supports=[()]*(25-triple)+[(0,1,2)]*triple
  for pair in combinations(range(3),2): supports += [pair]*(1-triple)
  for i in range(3): supports += [(i,)]*(6+triple)
 l=49-h
 B=s.Matrix([[int(i in z) for z in supports] for i in range(h)])
 one=s.ones(l,1);t=B.T*s.ones(h,1);R=s.ones(1,l).col_join(B)
 piv=[supports.index(())]+[supports.index((i,)) for i in range(h)]
 free=[i for i in range(l) if i not in piv]
 R0=R[:,piv];assert abs(R0.det())==1
 K=s.zeros(l,len(free))
 for j,col in enumerate(free):
  K[col,j]=1
  z=-R0.inv()*R[:,col]
  for k,row in enumerate(piv): K[row,j]=z[k]
 assert R*K==s.zeros(h+1,len(free))
 assert all(x.q==1 for x in K)
 v=alpha*one+beta*t
 assert all(x%prime==0 for x in R*v)
 coords=s.Matrix([v[j] for j in free])
 assert all(x%prime==0 for x in v-K*coords)
 assert any(x%prime!=0 for x in v)
 # C1=7*1-t and Ct=h*1 determine the following eigenvector residual.
 err=(7*alpha+h*beta-lam*alpha)*one+(-alpha-lam*beta)*t
 assert all(x%prime==0 for x in err)
 lattice_det=int((K.T*K).det())
 assert lattice_det==7**(h-1)*(343-22*h-h*h)
 mod7_rank=0
 if h==3:
  X=s.Matrix([[1,0],[0,1],[-1,-1]])
  W=B.T*X
  assert B*W==7*X and s.ones(1,l)*W==s.zeros(1,2)
  assert s.ones(l,h)*X==s.zeros(l,2) # CW=JX from CB^T=J.
  assert all(x%7==0 for x in R*W)
  coordinates=W[free,:]
  assert all(x%7==0 for x in W-K*coordinates)
  singleton_rows=[next(j for j in free if supports[j]==(i,)) for i in (0,1)]
  assert W[singleton_rows,:]==s.eye(2)
  mod7_rank=2
 rows.append(dict(h=h,triple_count=triple,prime=prime,eigenvalue=lam,
  exact_kernel_lattice_determinant=lattice_det,mod7_kernel_lower_bound=mod7_rank,
  residual_constant_divisor=7**mod7_rank,
  adjacency_determinant_divisor=(49-h)*7**(h-1+mod7_rank),
  vector_coefficients=[alpha,beta],unimodular_minor=int(R0.det()),
  kernel_rank=K.cols,orthogonality_vector=list(map(int,R*v)),
  eigenvector_error_coefficients=[7*alpha+h*beta-lam*alpha,-alpha-lam*beta]))
result=dict(scope="Integral kernel basis and formal eigenvector identities only; residual characteristic-polynomial implication is paper proof",profiles=rows)
Path(__file__).with_suffix(".json").write_text(json.dumps(result,indent=2)+"\n")
print(json.dumps(result,indent=2))
