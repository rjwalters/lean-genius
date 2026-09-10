"""Polynomial controls only; no residual spectrum or graph supplied."""
import json
from itertools import product
from pathlib import Path
import sympy as s
x=s.symbols("x");f=x*x-7*x+1;q=x*x+x+1
red=lambda p:s.rem(s.expand(p),f,x)
zero=lambda p,m:all(int(c)%m==0 for c in s.Poly(s.expand(p),x).all_coeffs())
assert red(q)==8*x
assert red(x*(7-x))==1
passed=failed=0
for bits in product((0,1),repeat=4):
 T=sum(bits[i]*x**i for i in range(4))
 for c,d in product(range(4),repeat=2):
  # A multiple of f calibrates independence from a chosen representative.
  R=c+d*x+f*(1+x*x)
  psi=s.expand(q*T*T+4*R)
  weighted=zero(red(psi-8*x*T.subs(x,7-x)),16)
  cyclotomic=zero(s.rem(psi,q,x),16)
  reduced=zero(red(R),4)
  assert weighted==cyclotomic==reduced
  if weighted: passed+=1
  else: failed+=1
C=s.zeros(48)
for i in range(0,8,2): C[i,i+1]=C[i+1,i]=1
for i in range(40):
 j=i//5;C[j,8+i]=C[8+i,j]=1
 for d in (1,2,3):
  j=(i+d)%40;C[8+i,8+j]=C[8+j,8+i]=1
t=s.Matrix([1]*8+[0]*40);one=s.ones(48,1)
assert C==C.T and all(C[i,i]==0 for i in range(48))
assert C*one==7*one-t and C*t==one
matrix_psi,remainder=s.div(C.charpoly(x).as_expr(),f,x)
assert remainder==0
matrix_remainder=s.rem(matrix_psi,q,x)
assert zero(matrix_remainder,16) and int(matrix_psi.subs(x,1))%5==0
cycle=[8,9,10,11]
assert all(C[cycle[j],cycle[(j+1)%4]]==1 for j in range(4))
matrix_control=dict(scope="Actual degree/support integer matrix, with explicit C4: not a q7 survivor",order=48,c4_cycle=cycle,cyclotomic_remainder=str(matrix_remainder),psi_coefficients=list(map(int,s.Poly(matrix_psi,x).all_coeffs())))
result=dict(scope="Conditional equivalence on polynomial controls satisfying Ihara congruence; no graph/spectrum existence",controls=passed+failed,pass_controls=passed,fail_controls=failed,matrix_control=matrix_control,condition="x²+x+1 divides psi modulo16")
Path(__file__).with_suffix(".json").write_text(json.dumps(result,indent=2)+"\n")
print(json.dumps(result,indent=2))
