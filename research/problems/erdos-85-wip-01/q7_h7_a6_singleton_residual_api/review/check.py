import pathlib,json,itertools,random,time,hashlib,sqlite3
import native,reference as ref
P=pathlib.Path(__file__).parent;A=pathlib.Path('/tmp/erdos85-sol1-h7-a6-singleton-complete-api');read=lambda p:json.loads(p.read_text());pins=read(A/'pins.json')
for f,h in pins.items():assert hashlib.sha256((A/f).read_bytes()).hexdigest()==h
c=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True);c.row_factory=sqlite3.Row
for old in read(A/'premises.json'):
 live=dict(c.execute('select * from review_requests where id=?',(old['id'],)).fetchone())
 for r in [old,live]:
  if isinstance(r['refs'],str):r['refs']=json.loads(r['refs'])
  r.pop('expired',None)
 assert old==live and live['resolution'].startswith('PASS')
old=pathlib.Path('/tmp/erdos85-sol1-h7-singleton-complete-native-api')
assert (A/'native.py').read_bytes()==(old/'native.py').read_bytes()
assert (A/'reference.py').read_text().split('def complete_domains')[1]==(old/'reference.py').read_text().split('def complete_domains')[1]
assert (A/'filter.cpp').read_text().split('void run(){')[1]==(old/'filter.cpp').read_text().split('void run(){')[1]
base=read(A/'source-fixture.json')['neighbors'];fixtures=[]
for seed in range(8120,8126):
 rng=random.Random(seed);hs=list(range(7));ls=list(range(7,49));rng.shuffle(hs);rng.shuffle(ls);p=hs+ls;g=[[] for _ in range(49)]
 for u,ns in enumerate(base):g[p[u]]=sorted(p[v] for v in ns)
 fixtures.append(g)
(P/'fixtures.json').write_text(json.dumps(fixtures)+'\n')
def pairings(xs):
 if not xs:yield [];return
 for j in range(1,len(xs)):
  for rest in pairings(xs[1:j]+xs[j+1:]):yield [(xs[0],xs[j])]+rest
rows=domains=comparisons=guards=invalid=0;start=time.monotonic()
for adj in fixtures:
 gm,support,E,U=ref.validate(adj);g=list(map(set,adj));full=ref.complete_domains(gm,support,U,ref.Budget(100000,time.monotonic()+60));assert full['status']=='DOMAINS_COMPLETE'
 S={u for u in U if support[u].bit_count()==1};same=[(u,v) for u in S for v in g[u]&S if u<v and support[u]==support[v]];assert same and all(len(g[u]&set(E))==len(g[v]&set(E))==2 for u,v in same)
 singles={h:[v for v in S if support[v]==1<<h] for h in range(7)};pairs={tuple(h for h in range(7) if support[v]>>h&1):v for v in U if support[v].bit_count()==2}
 for u in U:
  missing=[h for h in range(7) if not g[u]&g[h]];need=7-len(g[u]);np=len(missing)-need;actual=set()
  for pc in itertools.combinations(missing,2*np):
   sc=[h for h in missing if h not in pc]
   if u in S and sc:continue
   for pm in pairings(list(pc)):
    pv=[pairs[tuple(sorted(e))] for e in pm]
    for sv in itertools.product(*(singles[h] for h in sc)):
     row=set(pv)|set(sv)
     if u in row or row&g[u]:continue
     ns=g[u]|row
     if len(ns)!=7 or any((g[v]-{u})&(g[w]-{u}) for v,w in itertools.combinations(ns,2)):continue
     actual.add(sum(1<<v for v in row))
  assert actual==set(full['initial'][u]);rows+=len(actual);domains+=1
 exact=ref.check(adj,max_nodes=100000)
 for budget in [0,1,2,7,31,exact['nodes']-1,exact['nodes'],100000]:
  assert native.check(adj,max_nodes=budget)==ref.check(adj,max_nodes=budget);comparisons+=1
 for api in [native,ref]:assert api.check(adj,deadline=time.monotonic()-1)['status']=='UNKNOWN';guards+=1
 bads=[];bad=[list(ns) for ns in adj];bad[0].append(0);bads.append(bad)
 u,v=same[0];bad=[list(ns) for ns in adj];bad[u].remove(v);bad[v].remove(u);bads.append(bad)
 for bad in bads:
  for api in [native,ref]:
   try:api.check(bad);raise AssertionError('invalid accepted')
   except ValueError:invalid+=1
bad=read(P.parent/'h7-singleton-complete-row-api/fixtures.json')[0]
for api in [native,ref]:
 try:api.check(bad);raise AssertionError('a7 accepted')
 except ValueError:invalid+=1
r=dict(status='PASS',fixtures=6,complete_domains=domains,rows=rows,whole_object_comparisons=comparisons,expired_guards=guards,invalid_rejections=invalid,pins=len(pins),seconds=time.monotonic()-start);(P/'results.json').write_text(json.dumps(r,indent=2)+'\n');print(r)
