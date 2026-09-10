import pathlib,json,gzip,hashlib,sqlite3,collections
P=pathlib.Path(__file__).parent;L=pathlib.Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3/h7-a9-closure');root=P.parent
load=lambda p:json.loads(p.read_text())
for f,h in load(L/'pins.json').items():assert hashlib.sha256((L/f).read_bytes()).hexdigest()==h
origins=load(L/'origins.json')
for f,h in origins.items():assert hashlib.sha256(pathlib.Path(f).read_bytes()).hexdigest()==h
c=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True);c.row_factory=sqlite3.Row
required={2064,2066,2068,2069,2070,2071,2073,2074,2075,2076};snapshots=load(L/'reviews.json');assert {r['id'] for r in snapshots}==required
for r in snapshots:
 live=dict(c.execute('select * from review_requests where id=?',(r['id'],)).fetchone())
 assert live['status']=='resolved' and live['resolution'].startswith('PASS')
 def normalized(row):
  row=dict(row);row.pop('expired',None)
  if isinstance(row.get('refs'),str):row['refs']=json.loads(row['refs'])
  return row
 assert normalized(r)==normalized(live)
full=load(pathlib.Path('/tmp/erdos85-sol1-h7-profile-partitions/remaining-results.json'))['results'];profiles=load(L/'profiles.json')
assert profiles==[r for r in full if (r['twins_adjacent'],r['profile_index']) in [(True,6),(False,14)]]
# Re-derive exact max-high profile selection from all22count profiles.
count_profiles=load(pathlib.Path('/tmp/erdos85-sol1-h7-host-profiles/results.json'))['results']
keys=[(r['twins_adjacent'],i) for r in count_profiles for i,p in enumerate(r['representatives']) if sum(p['empty_counts'][:2])<=1]
assert keys==[(True,6),(False,14)]
seeds=load(L/'seeds.json');names=seeds['names'];ix={n:i for i,n in enumerate(names)};hosts=[ix[n] for n in ['S0a','S0b']+['P0'+str(c) for c in range(1,7)]]
local=load(pathlib.Path('/tmp/erdos85-sol1-h7-crossed14-local/results.json'))
with gzip.open(root/'h7-crossed14-arc/results.json.gz','rt') as f:crossarc=json.load(f)
with gzip.open(root/'h7-twin6-arc/results.json.gz','rt') as f:twin=json.load(f)
arc={r['source_index']:r for r in crossarc['results']};assert len(arc)==448
independent32=load(root/'h7-crossed14-cover-audit/results.json');assert independent32['cover']['status']=='COMPLETE' and independent32['positive_adjacency_matches']==448
for f,h in load(root/'h7-crossed14-cover-audit/input-pins.json').items():assert hashlib.sha256(pathlib.Path(f).read_bytes()).hexdigest()==h
negative32=set(independent32['negative_assignments']);assert len(negative32)==32
results=[];matched=0;no_graph=0;endpoints=collections.Counter()
for profile in profiles:
 t=profile['twins_adjacent'];source=twin['results'] if t else local['results'];N=2640 if t else 480
 assert len(source)==N and [r['assignment_index'] for r in source]==list(range(N))
 projections=load(L/('twin6-endpoints.json' if t else 'crossed14-endpoints.json'));assert len(projections)==N
 seed=next(s for s in seeds['patterns'] if s['twins_adjacent']==t);base=list(map(set,seed['adjacency']))
 for i,(assignment,r,p) in enumerate(zip(profile['assignments'],source,projections)):
  assert p['assignment_index']==i
  if t:expected='LOCAL' if r['status']=='INFEASIBLE_LOCAL' else 'ARC';assert r['status'] in ['INFEASIBLE_LOCAL','INFEASIBLE_ARC']
  elif r['status']=='INFEASIBLE':expected='LOCAL';assert i in negative32 and i not in arc
  else:expected='ARC';assert r['status']=='LOCAL_FEASIBLE' and arc[i]['status']=='INFEASIBLE_ARC'
  assert expected==p['endpoint'];endpoints[(t,expected)]+=1
  # Derive colour-slot ownership from seed mates and pair supports.
  g=[s.copy() for s in base];used=[]
  def edge(u,v):g[u].add(v);g[v].add(u)
  for h,m in zip(hosts,assignment):
   colours=set()
   for e,(a,b) in enumerate(profile['edge_order']):
    if m>>e&1:edge(h,ix[f'P{a}{b}']);colours|={a,b}
   mate=next(iter(base[h]&set(hosts)));used.append(set(range(1,7))-(base[mate]&set(range(7)))-colours)
  for colour in range(1,7):
   slots=[h for h,cs in zip(hosts,used) if colour in cs];assert len(slots)==2
   for letter,h in zip('ab',slots):edge(h,ix[f'S{colour}{letter}'])
  e=0
  for h,n in zip(hosts,profile['profile']['empty_counts']):
   for _ in range(n):edge(h,ix[f'E{e}']);e+=1
  assert e==7
  adj=[sorted(ns) for ns in g];digest=hashlib.sha256(json.dumps(adj,separators=(',',':')).encode()).hexdigest()
  if 'adjacency' in r:assert adj==r['adjacency'] and digest==p['graph_sha256'];matched+=1
  else:assert not t and expected=='LOCAL' and p['graph_sha256'] is None and i in negative32 and p['vertex']==r['vertex'];no_graph+=1
  results.append(dict(profile=[t,profile['profile_index']],assignment_index=i,endpoint=expected,reconstructed_graph_sha256=digest))
assert matched==3088 and no_graph==32 and results==load(L/'results.json')['rows']
assert endpoints=={(True,'LOCAL'):61,(True,'ARC'):2579,(False,'LOCAL'):32,(False,'ARC'):448}
out=dict(status='PASS',profiles=keys,assignment_count=3120,source_graph_matches=matched,previous_independent_local_negatives_bound=no_graph,accepted_reviews=sorted(required),ledger_payload_pins=len(load(L/'pins.json')),origin_pins=len(origins),scope='H7a9 excluded under reviewed graph premises. Other a-values,H1,Lean/global remain open.')
(P/'results.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
