"""Exact checks of a necessary H1 component quotient, not graph existence."""
import json
from itertools import permutations,product
from pathlib import Path
import sympy as s
a,X,Y=s.symbols("a X Y")
f=a*a-7*a+1
red=lambda p:s.rem(s.expand(p),f,a)
r=a-1;b=7-a
assert red(a*b)==1
assert red(6*a*a-2*a+1)==40*a-5
assert red((X-7*Y+a*Y)*(a-1)-(a*(X-Y)-X+6*Y))==0
assert red(a*a-b-8*r)==0
assert red(r*r+1-b-6*r)==0
survivors=[];systems=0
for c in range(1,5):
 inv=[p for p in permutations(range(c)) if all(p[p[i]]==i for i in range(c))]
 for k in product((2,4,6,8),repeat=c):
  if sum(k)!=8: continue
  for F,H in product(inv,repeat=2):
   if any(k[i]!=k[F[i]] or k[i]!=k[H[i]] for i in range(c)): continue
   systems+=1
   lhs=[[6*int(i==j)+int(F[H[i]]==j)+int(H[F[i]]==j) for j in range(c)] for i in range(c)]
   if all(lhs[i][j]==k[j] for i in range(c) for j in range(c)):
    survivors.append(dict(c=c,k=k,F=F,H=H))
assert len(survivors)==1 and survivors[0]['c']==1
out=dict(scope="Integer quotient constraints only; graph-to-quotient is paper proof",systems_checked=systems,surviving_quotient_systems=survivors)
Path(__file__).with_suffix(".json").write_text(json.dumps(out,indent=2)+"\n")
print(json.dumps(out,indent=2))
