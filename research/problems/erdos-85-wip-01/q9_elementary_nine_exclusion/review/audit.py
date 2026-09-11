from pathlib import Path
from itertools import permutations,product,combinations
import json,hashlib,math,time
p=Path(__file__).resolve().parent;s=Path('/tmp/erdos85-sol1-q9-elementary-nine-character');start=time.monotonic()
for f,h in json.loads((s/'pins.json').read_text()).items():assert hashlib.sha256((s/f).read_bytes()).hexdigest()==h
# Exact Eisenstein arithmetic a+b*omega, omega^2=-1-omega.
def add(x,y):return (x[0]+y[0],x[1]+y[1])
def neg(x):return (-x[0],-x[1])
def mul(x,y):return (x[0]*y[0]-x[1]*y[1],x[0]*y[1]+x[1]*y[0]-x[1]*y[1])
def conj(x):return (x[0]-x[1],-x[1])
def Z(x):return (x,0)
def det(A):
 n=len(A);out=Z(0)
 for sigma in permutations(range(n)):
  v=Z((-1)**sum(sigma[i]>sigma[j] for i in range(n) for j in range(i+1,n)))
  for i in range(n):v=mul(v,A[i][sigma[i]])
  out=add(out,v)
 return out
lines=[(1,0),(0,1),(1,1),(1,2)];pairs=list(combinations(range(4),2));omega=[(1,0),(0,1),(-1,-1)]
def chi(k,v):a,b=lines[k];x,y=v;return omega[(a*y-b*x)%3]
def eig(k,line):z=chi(k,lines[line]);v=add(z,conj(z));assert v[1]==0;return v[0]
F=set();S=set();T=set();checks=[0,0,0]
for u,v,w in product(range(4),repeat=3):
 for k in range(4):
  x=8-eig(k,u);y=8-eig(k,v);g=add(Z(1),chi(k,lines[w]));norm=mul(g,conj(g));assert norm==(4 if k==w else 1,0)
  if k==0:A=[[Z(9),Z(-3),Z(0)],[Z(-1),Z(x),neg(g)],[Z(0),neg(conj(g)),Z(y)]];formula=(9*x-3)*y-9*norm[0]
  elif k==1:A=[[Z(x),neg(g),Z(0)],[neg(conj(g)),Z(y),Z(-1)],[Z(0),Z(-3),Z(9)]];formula=(9*y-3)*x-9*norm[0]
  else:A=[[Z(x),neg(g)],[neg(conj(g)),Z(y)]];formula=x*y-norm[0]
  assert det(A)==Z(formula);checks[0]+=1
  if k==0:F.add(formula)
for pair in pairs:
 for k in range(4):
  r=sum(eig(k,line) for line in pair);A=[[Z(8-r),Z(-1)],[Z(-1),Z(8-r)]];value=det(A);assert value==Z((8-r)**2-1);checks[1]+=1
  if k==0:S.add(value[0])
for u in range(4):
 for leafpairs in product(pairs,repeat=3):
  for k in range(4):
   z=8-eig(k,u);v=[8-sum(eig(k,line) for line in pair) for pair in leafpairs];A=[[Z(0) for j in range(4)] for i in range(4)];A[0][0]=Z(z)
   for i in range(3):A[i+1][i+1]=Z(v[i]);A[0][i+1]=A[i+1][0]=Z(-1)
   value=det(A);formula=z*math.prod(v)-sum(v[i]*v[j] for i,j in combinations(range(3),2));assert value==Z(formula);checks[2]+=1
   if k==0:T.add(value[0])
assert len(F)==8 and len(S)==2 and len(T)==8
assert all(math.isqrt(f*s*t)**2!=f*s*t for f,s,t in product(F,S,T))
r={'status':'PASS_EXACT_COMPONENT_DETERMINANTS','component_checks':checks,'F':sorted(F),'S':sorted(S),'T':sorted(T),'products_checked':128,'all_nonsquare':True,'seconds':time.monotonic()-start,'scope':'component formulas plus arithmetic; graph reduction reviewed separately'}
(p/'results.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r))
