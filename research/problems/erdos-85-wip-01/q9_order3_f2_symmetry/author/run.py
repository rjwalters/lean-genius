from pathlib import Path
import json,itertools,hashlib
p=Path(__file__).parent;src=Path('/tmp/erdos85-sol1-q9-order3-f2-contingency/receipts.json');rs=json.loads(src.read_text())
def key(k,P,m,T):return (k,*P,*((-1,-1) if m is None else m),*(v for row in T for v in row))
records={key(r['cross_orbits'],r['mapping'],r['missing_labels'],T):{'state':i,'table':j} for i,r in enumerate(rs) for j,T in enumerate(r['tables'])};assert len(records)==672
orbs={};covered=set()
for w in records:
 k=w[0];P=w[1:4];missing=w[4:6];T=[w[6+3*i:9+3*i] for i in range(3)];orbit=set()
 for a,b,swap in itertools.product([(0,1,2),(0,2,1)],[(0,1,2),(0,2,1)],(False,True)):
  q=[-1]*3;t=[[0]*3 for _ in range(3)]
  for i,v in enumerate(P):
   if v>=0:q[a[i]]=b[v]
  for i in range(3):
   for j in range(3):t[a[i]][b[j]]=T[i][j]
  m=None if missing==(-1,-1) else(a[missing[0]],b[missing[1]])
  if swap:
   inv=[-1]*3
   for i,v in enumerate(q):
    if v>=0:inv[v]=i
   q=inv;t=[list(x) for x in zip(*t)];m=None if m is None else m[::-1]
  orbit.add(key(k,q,m,t))
 assert orbit<=records.keys();canon=min(orbit)
 if canon not in orbs:
  assert not orbit&covered;covered|=orbit;orbs[canon]=orbit
assert covered==records.keys()
result=[{'key':list(k),'size':len(v),**records[k]} for k,v in sorted(orbs.items())]
(p/'orbits.json').write_text(json.dumps(result)+'\n');(p/'input-pin.json').write_text(json.dumps({'path':str(src),'sha256':hashlib.sha256(src.read_bytes()).hexdigest()},indent=2)+'\n');print('Complete:',len(result),'orbits cover',len(covered),'tables')
