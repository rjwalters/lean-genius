from pathlib import Path
import json,itertools,hashlib,sqlite3,time,collections
P=Path('/Users/rwalters/lean-genius-q7-outside-first-20260910/h7-a7-noncycle-singleton-projection');O=Path(__file__).parent;start=time.monotonic()
read=lambda f:json.loads((P/f).read_text())
pins=read('pins.json');origins=read('origins.json')
for f,h in pins.items():assert hashlib.sha256((P/f).read_bytes()).hexdigest()==h
for f,h in origins.items():assert hashlib.sha256(Path(f).read_bytes()).hexdigest()==h
c=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True);c.row_factory=sqlite3.Row
for old in read('premises.json'):
 live=dict(c.execute('select * from review_requests where id=?',(old['id'],)).fetchone());assert live==old and live['status']=='resolved' and live['resolution'].startswith('PASS')
source=read('source.json');cover=read('results.json');done=read('completion-results.json')
expected=[(i,r) for i,r in enumerate(source['classes']) if r['edge_count']==7 and r['degree_sequence']!=[2]*7]
assert [i for i,r in expected]==[f['F_index'] for f in cover['F_classes']]
K=list(itertools.combinations(range(7),2));nraw=0;nreps=0
for (fi,original),f in zip(expected,cover['F_classes']):
 F=set(map(tuple,original['edges']));assert F==set(map(tuple,f['F_edges']))
 neighbors=[{v for v in range(7) if tuple(sorted((u,v))) in F} for u in range(7)]
 allowed=[e for e in K if not neighbors[e[0]]&neighbors[e[1]]];caps=[7-2*len(n) for n in neighbors]
 raw=set()
 def enum(i,left,degs,edges):
  if left==0:raw.add(tuple(edges));return
  if len(allowed)-i<left:return
  u,v=allowed[i]
  enum(i+1,left,degs,edges)
  if degs[u]<caps[u] and degs[v]<caps[v]:
   nd=degs[:];nd[u]+=1;nd[v]+=1;enum(i+1,left-1,nd,edges+[allowed[i]])
 enum(0,7,[0]*7,[])
 perms=[p for p in itertools.permutations(range(7)) if {tuple(sorted((p[u],p[v]))) for u,v in F}==F]
 seen=set();reps=[r for r in cover['representatives'] if r['F_index']==fi]
 for r in reps:
  edges=tuple(map(tuple,r['edges']));assert r['F_edges']==f['F_edges'] and r['mask']==sum(1<<allowed.index(e) for e in edges)
  orbit={tuple(sorted(tuple(sorted((p[u],p[v]))) for u,v in edges)) for p in perms}
  assert orbit<=raw and not seen&orbit and len(orbit)==r['orbit_size'];seen|=orbit
  hosts=[list(e) for e in edges]
  for u in range(7):hosts += [[u]]*(caps[u]-sum(u in e for e in edges))
  assert hosts==r['singleton_hosts'] and len(hosts)==14
 assert seen==raw and len(raw)==f['raw'] and len(reps)==f['orbits'] and len(perms)==f['aut_F']
 nraw+=len(raw);nreps+=len(reps)
valid=0
for i,r in enumerate(done['results']):
 assert r['source_index']==i
 base=cover['representatives'][i];assert r['F_index']==base['F_index']
 g0=[0]*21
 def edge(g,u,v):g[u]|=1<<v;g[v]|=1<<u
 for u,v in base['F_edges']:edge(g0,u,v)
 for u,hosts in enumerate(base['singleton_hosts'],7):
  for v in hosts:edge(g0,u,v)
 solutions=set()
 for es in r['solutions']:
  code=tuple(map(tuple,es));assert len(code)==14 and len(set(code))==14 and code not in solutions;solutions.add(code)
  g=g0[:]
  for u,v in code:assert 7<=u<v<21;edge(g,u,v)
  assert all(g[u].bit_count()==5-g0[u].bit_count() for u in range(7,21))
  assert all((g[u]&g[v]).bit_count()<=1 for u in range(21) for v in range(u))
  valid+=1
 assert r['count']==len(solutions)
 assert r['status']==('COMPLETE' if i<860 else 'UNKNOWN')
 if i<860:assert r['nodes']<=100000
summary=done['summary'];assert len(done['results'])==861 and nreps==1310 and valid==46728
assert summary['counts']=={'COMPLETE':860,'UNKNOWN':1} and summary['unvisited']==449 and summary['solutions']==valid
out=dict(status='PASS',source_pins=len(pins),origin_pins=len(origins),F_classes=len(expected),X_raw=nraw,X_orbits=nreps,complete=860,unknown=1,unvisited=449,valid_extensions=valid,seconds=time.monotonic()-start,scope='Independent recursive capacity-cover and explicit AutF orbits; every host join and saved graph checked with bitwise common-neighbor test. No S completion rerun; terminal completeness rests on audited exhaustive star traversal, with unresolved frontier preserved.')
(O/'results.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
