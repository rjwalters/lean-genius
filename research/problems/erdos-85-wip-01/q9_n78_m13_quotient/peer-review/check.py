from pathlib import Path
from itertools import product,permutations
import hashlib,json,time
s=Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3/q9-n78-m13-quotient');p=Path(__file__).parent
pins=json.loads((s/'pins.json').read_text())
for f,h in pins.items():assert hashlib.sha256((s/f).read_bytes()).hexdigest()==h
src=json.loads((s/'results.json').read_text());assert src['status']=='COMPLETE' and src['unvisited_cases']==0
start=time.monotonic();domains=[]
# Deliberately include4 and force the diagonal from the cross row sum.
for i in range(6):
 rows=[]
 for cross in product(range(5),repeat=5):
  a=9-sum(cross)
  if a not in (0,2) or a*a+sum(x*x for x in cross)>21:continue
  row=list(cross);row.insert(i,a);rows.append(tuple(row))
 domains.append(rows)
assert all(len(d)==190 for d in domains)
found=set();nodes=0

def visit(assigned,possible):
 global nodes
 nodes+=1
 assert nodes<100000 and time.monotonic()-start<60,'verification cap, no retry'
 if len(assigned)==6:
  q=tuple(assigned[i] for i in range(6));found.add(q);return
 i=min(possible,key=lambda j:len(possible[j]))
 for row in possible[i]:
  nxt={};valid=True
  for j,rs in possible.items():
   if j==i:continue
   nr=[r for r in rs if row[j]==r[i] and sum(a*b for a,b in zip(row,r))<=13]
   if not nr:valid=False;break
   nxt[j]=nr
  if valid:visit({**assigned,i:row},nxt)
visit({},dict(enumerate(domains)))
expected=set()
for q in src['matrices']:
 for perm in permutations(range(6)):expected.add(tuple(tuple(q[i][j] for j in perm) for i in perm))
assert found==expected and len(found)==70
classes={min(tuple(tuple(q[i][j] for j in perm) for i in perm) for perm in permutations(range(6))) for q in found}
assert len(classes)==2
for q in found:
 assert all(sum(q[i][k]*q[j][k] for k in range(6))==(21 if i==j else 12) for i in range(6) for j in range(6))
result=dict(status='PASS',labelled=70,classes=2,states=nodes,seconds=time.monotonic()-start,method='all labelled row domains including4; dynamic smallest-domain join and symmetric/dot propagation; no first-row sorting')
(p/'results.json').write_text(json.dumps(result,indent=2)+'\n');(p/'source-pins.json').write_text(json.dumps(pins,indent=2)+'\n');print(result)
