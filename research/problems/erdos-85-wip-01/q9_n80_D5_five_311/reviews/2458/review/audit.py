from pathlib import Path
import itertools as I,json,hashlib,sqlite3,time,collections
p=Path(__file__).parent;src=Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3/residual-ten-D5-shapes');read=lambda f:json.loads(f.read_text());checks={}
for mf in [src/'pins.json']:
 for name,h in read(mf).items():
  f=mf.parent/name;assert hashlib.sha256(f.read_bytes()).hexdigest()==h;checks[str(f)]=h
con=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True);con.row_factory=sqlite3.Row
premise=dict(con.execute('select id,status,resolution from review_requests where id=2295').fetchone());assert premise['status']=='resolved' and premise['resolution'].startswith('PASS')
saved=read(src/'results.json');assert saved['status']=='COMPLETE';expected={tuple(map(tuple,r['edges'])):r for r in saved['records']};assert len(expected)==len(saved['records'])==1041
start=time.monotonic();good=set();tested=0;orbitchecks=[];status='INCOMPLETE'
def guard():
 if time.monotonic()-start>30:raise TimeoutError
try:
 orbits=sorted({tuple(sorted({(a,b),tuple(sorted((a^1,b^1)))})) for a,b in I.combinations(range(10),2)})
 assert collections.Counter(map(len,orbits))=={1:5,2:20}
 def choose(pos,left,edges):
  global tested
  guard()
  if left==0:
   tested+=1;E=tuple(sorted(edges));adj=[set() for _ in range(10)]
   for a,b in E:adj[a].add(b);adj[b].add(a)
   if max(map(len,adj))>3:return
   paths=set()
   for neighbors in adj:
    for pair in I.combinations(sorted(neighbors),2):
     if pair in paths:return
     paths.add(pair)
   good.add(E)
   # Independent union-find detects any cycle.
   parent=list(range(10))
   def find(v):
    while parent[v]!=v:v=parent[v]
    return v
   for a,b in E:
    a=find(a);b=find(b);assert a!=b;parent[a]=b
   assert E in expected
   pattern=sorted(len(adj[v]) for v in range(0,10,2));assert pattern==expected[E]['pattern']
   return
  for j in range(pos,len(orbits)):
   if len(orbits[j])<=left:choose(j+1,left-len(orbits[j]),edges+orbits[j])
 choose(0,5,tuple())
 assert tested==1151 and good==set(expected)
 maps=[tuple(2*pi[v//2]+((v%2)^flips[v//2]) for v in range(10)) for pi in I.permutations(range(5)) for flips in I.product(range(2),repeat=5)]
 assert len(set(maps))==3840 and all(all(g[v^1]==(g[v]^1) for v in range(10)) for g in maps)
 covered=set()
 for cl in saved['classes']:
  guard();rep=list(map(tuple,cl['representative']))
  orbit={tuple(sorted(tuple(sorted((g[a],g[b]))) for a,b in rep)) for g in maps}
  claimed={E for E,r in expected.items() if r['key']==cl['key']}
  assert orbit==claimed and not orbit&covered and len(orbit)==cl['multiplicity']
  covered|=orbit;orbitchecks.append({'pattern':cl['pattern'],'representative':rep,'size':len(orbit)})
 assert covered==good and len(orbitchecks)==8
 counts=collections.Counter(tuple(r['pattern']) for r in expected.values())
 assert sorted(counts.items())==[((0,0,1,1,3),120),((0,0,1,2,2),240),((0,1,1,1,2),600),((1,1,1,1,1),81)]
 status='COMPLETE'
except TimeoutError:pass
r={'status':status,'original_cap_seconds':30,'seconds':time.monotonic()-start,'hashes':checks,'premise':premise,'tested':tested,'graphs':len(good),'classes':orbitchecks};(p/'results.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({'status':status,'seconds':r['seconds'],'hashes':len(checks),'tested':tested,'graphs':len(good),'orbits':[c['size'] for c in orbitchecks]}))
