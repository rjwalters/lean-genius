from pathlib import Path
import itertools,json,gzip,hashlib,time
p=Path(__file__).parent;start=time.monotonic();roots=[]
for a in range(3):
 for xs in itertools.combinations_with_replacement(range(4),9):
  if a+sum(xs)==9 and a*a+sum(x*x for x in xs)<=15:roots.append((a,)+xs)
assert len(roots)==13
seen=[set() for _ in roots];cases=[];summary=None
for l in gzip.open(p/'receipts.jsonl.gz','rt'):
 r=json.loads(l)
 if 'matrix' not in r:
  if 'case' in r:cases.append(r)
  else:summary=r
  continue
 q=r['matrix'];root=r['root'];assert len(q)==10 and all(len(row)==10 for row in q)
 assert tuple(q[0])==roots[root];key=tuple(map(tuple,q));assert key not in seen[root];seen[root].add(key)
 for i in range(10):
  assert sum(q[i])==9 and 0<=q[i][i]<=2
  for j in range(10):
   assert q[i][j]==q[j][i] and 0<=q[i][j]<=3
   assert sum(q[i][k]*q[k][j] for k in range(10))<=(15 if i==j else 8)
   if i!=j and q[i][i]==q[j][j]==1:assert q[i][j]==0
  if (9-q[i][i])%2:assert any(q[i][j] and sum(q[i][k]*q[k][j] for k in range(10))<8 for j in range(10) if j!=i)
 # Exhaust all binary colourings, independently of producer BFS.
 vertices=[i for i in range(10) if q[i][i]==2]
 assert any(all(not q[u][v] or colors[a]!=colors[b] for a,u in enumerate(vertices) for b,v in enumerate(vertices) if a<b) for colors in itertools.product([0,1],repeat=len(vertices)))
assert len(cases)==13
for i,r in enumerate(cases):assert r['case']==i and r['status']=='UNKNOWN' and r['reason']=='nodes' and r['nodes']==100000 and r['retained']==len(seen[i])
assert summary['visited']==summary['unknown']==13 and summary['unvisited']==0 and summary['retained']==sum(map(len,seen))==24
launch=json.loads((p/'launch.json').read_text())
assert hashlib.sha256((p/'cover.cpp').read_bytes()).hexdigest()==launch['source_sha256']
assert hashlib.sha256((p/'cover').read_bytes()).hexdigest()==launch['binary_sha256']
r={'status':'PASS_RETAINED_ONLY','matrices':24,'unknown_roots':13,'complete_roots':0,'seconds':time.monotonic()-start,'scope':'Saved quotient constraints and status fidelity only; no capped-domain replay/completeness/exclusion'}
(p/'verification.json').write_text(json.dumps(r,indent=2)+'\n');print(r)
