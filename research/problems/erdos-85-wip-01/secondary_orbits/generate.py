from itertools import product,permutations
from pathlib import Path
import json
base=Path(__file__).parent

def adj(t):
 m,a,b,e=t;m+=1;B=[[False]*8 for _ in range(8)]
 for i in range(m):B[2*i][2*i+1]=B[2*i+1][2*i]=True
 for k,x in enumerate((a,b)):
  if x:B[6+k][x-1]=B[x-1][6+k]=True
 B[6][7]=B[7][6]=bool(e)
 return B

def allowed(t):
 B=adj(t)
 return (sum(B[i][j] for i in range(8) for j in range(i+1,8)) in (3,4)
  and all(sum(B[i][k] and B[j][k] for k in range(8))<=1 for i in range(8) for j in range(i+1,8))
  and all(x or t[3] for x in t[1:3]))
raw=list(product(range(3),range(7),range(7),range(2)))
valid=[t for t in raw if allowed(t)];assert len(valid)==132
maps={}
for m in range(3):
 def edge(i,j):return i!=j and i//2==j//2 and i<2*(m+1)
 maps[m]=[p for p in permutations(range(6)) if all(edge(i,j)==edge(p[i],p[j]) for i in range(6) for j in range(6))]
canonical={}
for t in valid:
 m,a,b,e=t;options=[]
 for p in maps[m]:
  aa=0 if not a else p[a-1]+1;bb=0 if not b else p[b-1]+1
  for swap in range(2):
   r=(m,bb,aa,e) if swap else (m,aa,bb,e)
   perm=p+((7,6) if swap else (6,7))
   assert allowed(r)
   B,C=adj(t),adj(r)
   assert all(B[i][j]==C[perm[i]][perm[j]] for i in range(8) for j in range(8))
   options.append((r,perm))
 canonical[t]=min(options)
reps=sorted({r for r,p in canonical.values()});assert len(reps)==21
witnesses=[]
for t in raw:
 r,p=canonical.get(t,(reps[0],tuple(range(8))))
 witnesses.append({'source':t,'representative':reps.index(r),'permutation':p,'admissible':t in canonical})
result={'raw_count':294,'admissible_count':132,'representative_count':21,'representatives':reps,'witnesses':witnesses}
(base/'witnesses.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='witnesses'}))
