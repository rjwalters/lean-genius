from pathlib import Path
import json,itertools,math,time,hashlib
p=Path(__file__).parent;src=Path('/tmp/erdos85-sol1-q9-order3-f2-contingency/receipts.json');states=json.loads(src.read_text());start=time.monotonic();rows=[];counts=[]
for si,r in enumerate(states):
 P=r['mapping'];edges=[(1,2),(4,5)]+[(a,3+b) for a,b in enumerate(P) if b>=0];parent=list(range(6));cycle=None
 def find(i):
  while parent[i]!=i:i=parent[i]
  return i
 for ei,(a,b) in enumerate(edges):
  x,y=find(a),find(b)
  if x==y:assert cycle is None;cycle=ei
  else:parent[x]=y
 for voltage in ([0] if cycle is None else [1,2]):
  adj=[set() for _ in range(18)]
  for ei,(a,b) in enumerate(edges):
   s=voltage if ei==cycle else 0
   for g in range(3):u=3*a+g;v=3*b+(g+s)%3;adj[u].add(v);adj[v].add(u)
  allowed=[[s for s in range(3) if not adj[3*a]&adj[9+3*b+s]] for a in range(3) for b in range(3)]
  assert list(map(len,allowed))==[v for row in r['capacities'] for v in row]
  for ti,T in enumerate(r['tables']):
   t=[v for row in T for v in row];choices=[[sum(1<<s for s in c) for c in itertools.combinations(allow,n)] for allow,n in zip(allowed,t)];expected=math.prod(map(len,choices));begin=len(rows)
   for masks in itertools.product(*choices):
    assert time.monotonic()-start<60
    assert all(m.bit_count()==n and m&~sum(1<<s for s in allow)==0 for m,n,allow in zip(masks,t,allowed))
    rows.append([si,ti,voltage,*masks])
   assert len(rows)-begin==expected;counts.append([si,ti,voltage,expected])
assert len(rows)==len(set(map(tuple,rows)))==56916
(p/'phase-parameters.json').write_text(json.dumps(rows)+'\n');(p/'counts.json').write_text(json.dumps(counts)+'\n');(p/'input-pin.json').write_text(json.dumps({'path':str(src),'sha256':hashlib.sha256(src.read_bytes()).hexdigest()},indent=2)+'\n')
result={'status':'COMPLETE','original_wall_cap':60,'seconds':time.monotonic()-start,'parameters':len(rows),'table_voltage_roots':len(counts),'tables':672}
(p/'results.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
