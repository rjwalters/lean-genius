from pathlib import Path
import json,itertools as I,hashlib,sqlite3,time
p=Path(__file__).parent;src=Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3/residual-ten-D5-supports');read=lambda f:json.loads(f.read_text());checks={}
for mf in [src/'pins.json',src/'input-pins.json']:
 for name,h in read(mf).items():
  f=mf.parent/name;assert hashlib.sha256(f.read_bytes()).hexdigest()==h;checks[str(f)]=h
con=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True);con.row_factory=sqlite3.Row
states=[dict(con.execute('select id,status,resolution from review_requests where id=?',(i,)).fetchone()) for i in [2251,2458]];assert all(r['status']=='resolved' and r['resolution'].startswith('PASS') for r in states)
classes=read(src.parent/'residual-ten-D5-shapes/results.json')['classes'];saved=read(src/'results.json');assert saved['status']=='COMPLETE';records=saved['records'];assert len(records)==8 and [r['class'] for r in records]==list(range(8))
start=time.monotonic();out=[];status='INCOMPLETE'
def flip(s):return tuple(sorted(v^1 for v in s))
def valid(edges,supports):
 adj=[set() for _ in range(10+len(supports))]
 for a,b in edges:adj[a].add(b);adj[b].add(a)
 for v,s in enumerate(supports,10):
  for e in s:adj[v].add(e);adj[e].add(v)
 endpoints=set()
 for row in adj:
  for pair in I.combinations(sorted(row),2):
   if pair in endpoints:return False
   endpoints.add(pair)
 return True
try:
 for ci,cl in enumerate(classes):
  if time.monotonic()-start>30:raise TimeoutError
  edges=cl['representative'];claim=records[ci];assert claim['edges']==edges and claim['pattern']==cl['pattern']
  degree=[sum(v in e for e in edges) for v in range(10)];domains={}
  for k in (2,3):
   accepted=set()
   for support in I.combinations(range(10),k):
    if sum(degree[v] for v in support)>k+2:continue
    if valid(edges,[support,flip(support)]):accepted.add(min(support,flip(support)))
   domains[k]=sorted(accepted);assert domains[k]==list(map(tuple,claim['high'+str(k)]))
  counts={}
  for k,l in [(2,2),(2,3),(3,3)]:
   compatible=[]
   index_pairs=I.combinations(range(len(domains[k])),2) if k==l else I.product(range(len(domains[k])),range(len(domains[l])))
   for i,j in index_pairs:
    if time.monotonic()-start>30:raise TimeoutError
    s,t=domains[k][i],domains[l][j]
    if valid(edges,[s,flip(s),t,flip(t)]):compatible.append([i,j])
   label=str(k)+str(l);assert compatible==claim['compatible_pairs'][label];counts[label]=len(compatible)
  out.append({'class':ci,'high2':len(domains[2]),'high3':len(domains[3]),'pairs':counts})
 status='COMPLETE'
except TimeoutError:pass
r={'status':status,'original_cap_seconds':30,'seconds':time.monotonic()-start,'hashes':checks,'premises':states,'records':out};(p/'results.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({'status':status,'seconds':r['seconds'],'hashes':len(checks),'records':out}))
