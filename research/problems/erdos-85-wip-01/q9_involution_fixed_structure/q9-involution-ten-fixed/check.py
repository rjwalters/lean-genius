from pathlib import Path
import itertools,json
p=Path(__file__).resolve().parent;out={}
for N in [78,80]:
 profiles=[]
 for c in itertools.product(range(11),repeat=4):
  counts=list(c)+[10-sum(c)]
  if min(counts)<0:continue
  degrees=[1,3,5,7,9];S=sum(n*r for n,r in zip(counts,degrees));R=N-100+S
  if R<0 or sum(n*r*(r-1) for n,r in zip(counts,degrees))>90:continue
  if any((9-r)*(r-2)>R for n,r in zip(counts,degrees) if n):continue
  expanded=[r for n,r in zip(counts,degrees) for _ in range(n)]
  if any(sum(sorted(d-1 for j,d in enumerate(expanded) if j!=i)[:r])>9 for i,r in enumerate(expanded)):continue
  profiles.append({'counts':counts,'S':S,'R':R})
 out[N]=profiles
assert [x['counts'] for x in out[78]]==[[0,10,0,0,0],[1,9,0,0,0]]
assert [x['counts'] for x in out[80]]==[[0,10,0,0,0],[1,7,2,0,0],[1,9,0,0,0],[2,5,3,0,0],[2,8,0,0,0]]
(p/'results.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
