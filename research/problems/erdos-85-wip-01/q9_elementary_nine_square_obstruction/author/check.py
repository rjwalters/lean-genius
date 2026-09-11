import itertools,math,json
from pathlib import Path
p=Path(__file__).parent
F=sorted({(9*x-3)*y-9*t for x,y,t in itertools.product((6,9),(6,9),(1,4))})
S=sorted({(8-d)**2-1 for d in (1,-2)})
T=sorted({z*math.prod(v)-sum(v[i]*v[j] for i,j in ((0,1),(0,2),(1,2))) for z in (6,9) for v in itertools.product((7,10),repeat=3)})
assert F==[270,297,423,432,450,459,666,693] and S==[48,99] and T==[1911,2751,2940,3960,4221,5700,6060,8700]
assert all(math.isqrt(f*s*t)**2!=f*s*t for f,s,t in itertools.product(F,S,T))
def sf(n):
 k=2;r=1
 while k*k<=n:
  odd=False
  while n%k==0:n//=k;odd=not odd
  if odd:r*=k
  k+=1
 return r*n
assert {sf(s*t) for s in S for t in (2940,3960)}=={5,165,330,10}
assert {sf(f) for f in F}.isdisjoint({5,165,330,10})
result={'status':'PASS','products':128,'F':F,'S':S,'T':T,'F_squarefree':[sf(f) for f in F]}
(p/'results.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
