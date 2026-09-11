from pathlib import Path
import itertools,json,gzip,time
p=Path(__file__).parent;start=time.monotonic();roots=[]
for a in range(3):
 for x in itertools.combinations_with_replacement(range(4),7):
  if a+sum(x)==9 and a*a+sum(t*t for t in x)<=18:roots.append((a,)+x)
assert len(roots)==16
seen=[set() for _ in roots];count=0;cases=[];summary=None
for line in gzip.open(p/'receipts.jsonl.gz','rt'):
 r=json.loads(line)
 if 'matrix' in r:
  q=r['matrix'];i=r['root'];assert tuple(q[0])==roots[i]
  assert len(q)==8 and all(len(row)==8 for row in q)
  assert all(sum(row)==9 and 0<=q[j][j]<=2 for j,row in enumerate(q))
  assert all(q[j][k]==q[k][j] and 0<=q[j][k]<=3 for j in range(8) for k in range(j))
  assert all(sum(q[j][h]*q[k][h] for h in range(8))<=(18 if j==k else 10) for j in range(8) for k in range(j+1))
  assert all(q[j][k]==0 for j in range(8) for k in range(j) if q[j][j]==q[k][k]==1)
  key=tuple(map(tuple,q));assert key not in seen[i];seen[i].add(key);count+=1
 elif 'case' in r:cases.append(r)
 else:summary=r
assert len(cases)==16 and all(r['case']==i and r['status']=='UNKNOWN' and r['reason']=='nodes' and r['nodes']==100000 and r['retained']==len(seen[i]) for i,r in enumerate(cases))
assert count==1998==summary['retained'] and summary['unknown']==16 and summary['unvisited']==0
result=dict(status='PASS_RETAINED_ONLY',matrices=count,unknown_roots=16,complete_roots=0,seconds=time.monotonic()-start,scope='valid retained matrices only; no complete quotient cover or exclusion')
(p/'verification.json').write_text(json.dumps(result,indent=2)+'\n');print(result)
