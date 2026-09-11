from pathlib import Path
import json,hashlib,sqlite3,random,time,math
import api,reference
P=Path(__file__).parent;S=Path('/tmp/erdos85-sol1-h7-a6-residual-batch-api');start=time.monotonic()
for f,h in json.loads((S/'pins.json').read_text()).items():assert hashlib.sha256((S/f).read_bytes()).hexdigest()==h
for f,h in json.loads((S/'origins.json').read_text()).items():assert hashlib.sha256(Path(f).read_bytes()).hexdigest()==h
assert (P/'filter.cpp').read_bytes()==Path('/tmp/erdos85-sol1-h7-a6-singleton-complete-api/filter.cpp').read_bytes()
c=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True);c.row_factory=sqlite3.Row;old=json.loads((S/'premise.json').read_text());live=dict(c.execute('select * from review_requests where id=?',(old['id'],)).fetchone());assert live==old and live['status']=='resolved' and live['resolution'].startswith('PASS')
original=json.loads((P.parent/'h7-a6-same-colour-fixture/fixture.json').read_text())['neighbors'];rng=random.Random(2126);fixtures=[]
for j in range(6):
 hs=list(range(7));ls=list(range(7,49));rng.shuffle(hs);rng.shuffle(ls);perm=hs+ls;adj=[[] for _ in range(49)]
 for u,ns in enumerate(original):adj[perm[u]]=[perm[v] for v in ns]
 fixtures.append(adj)
# Two already generated, independently checked host fixtures from review2123.
b=json.loads((P.parent/'h7-monotone-host-prefix-verifier/fixture.json').read_text());rr=json.loads((P.parent/'review2123/unrestricted-receipt.json').read_text())
for chosen in rr['solutions'][:2]:
 g=list(map(set,b['base']))
 for e,m in zip(b['empty_vertices'],chosen):
  for v in range(49):
   if m>>v&1:g[e].add(v);g[v].add(e)
 fixtures.append([sorted(ns) for ns in g])
comparisons=guards=0;records=[]
for adj in fixtures:
 g,support,E,U=reference.validate(adj);pv=[u for u in U if support[u].bit_count()==2];fixed=[sum(1<<v for v in pv if g[e]>>v&1) for e in E];base=list(map(set,adj))
 for e in E:
  for v in pv:base[e].discard(v);base[v].discard(e)
 full=reference.check(adj,max_nodes=100000)
 for cap in sorted({0,1,2,full['nodes']//2,full['nodes']-1,full['nodes'],100000}):
  expected=reference.check(adj,max_nodes=cap)
  if expected['status']=='INFEASIBLE_ROW':expected={k:expected[k] for k in ['status','empty_vertex','nodes']}
  assert api.check_hosts(base,E,[fixed],max_nodes=cap)==[expected];comparisons+=1
 z=api.check_hosts(base,E,[fixed,fixed],max_nodes=0);assert len(z)==2 and all(r['status']=='UNKNOWN' for r in z);guards+=1
 assert api.check_hosts(base,E,[fixed],deadline=time.monotonic()-1)==[];guards+=1
 assert api.check_hosts(base,E,[])==[];guards+=1
 for params in [dict(max_nodes=-1),dict(max_nodes=2**31),dict(deadline=math.nan)]:
  try:api.check_hosts(base,E,[fixed],**params)
  except ValueError:guards+=1
  else:raise AssertionError('invalid budget accepted')
 for empties,assign in [(E[:6]+[E[0]],[fixed]),(E,[[1]+fixed[1:]]),(E,[[(1<<49)]+fixed[1:]])]:
  try:api.check_hosts(base,empties,assign)
  except ValueError:guards+=1
  else:raise AssertionError('invalid shape accepted')
 records.append(dict(status=full['status'],nodes=full['nodes']))
out=dict(status='PASS',fixtures=len(fixtures),comparisons=comparisons,guards=guards,results=records,seconds=time.monotonic()-start,scope='Independently compiled adapter, six new high/low relabel fixtures and two existing review2123host fixtures; exact compact/full JSON against2120reference, no family residual pass.')
(P/'results.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
