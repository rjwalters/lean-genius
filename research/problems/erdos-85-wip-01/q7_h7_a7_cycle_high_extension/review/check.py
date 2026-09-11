import pathlib,json,gzip,itertools,hashlib,sqlite3,time,collections
P=pathlib.Path(__file__).parent;A=pathlib.Path('/tmp/erdos85-sol1-h7-projection-extension');S=P.parent/'h7-a7-cycle-singleton-host-projection';read=lambda p:json.loads(p.read_text());pins=read(A/'pins.json')
for f,h in pins.items():assert hashlib.sha256((A/f).read_bytes()).hexdigest()==h
for f in ['results.json','completion-results.json','pins.json']:assert (A/('source-'+f)).read_bytes()==(S/f).read_bytes()
with gzip.open(A/'results.json.gz','rb') as f:raw=f.read()
assert hashlib.sha256(raw).digest()==hashlib.sha256((A/'results.json').read_bytes()).digest();data=json.loads(raw);del raw
c=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True);c.row_factory=sqlite3.Row
for old in read(A/'premises.json'):
 live=dict(c.execute('select * from review_requests where id=?',(old['id'],)).fetchone());assert old==live and live['resolution'].startswith('PASS')
cover=read(S/'results.json');comp=read(S/'completion-results.json');source={(r['source_index'],j):es for r in comp['results'] for j,es in enumerate(r['solutions'])};assert len(source)==459
K=list(itertools.combinations(range(7),2));ki={e:i for i,e in enumerate(K)};out=[];start=time.monotonic();seen=set();direct=0
for r in data['results']:
 assert time.monotonic()-start<60 and r['status']=='COMPLETE'
 key=(r['source_index'],r['singleton_index']);assert key not in seen;seen.add(key);rep=cover['representatives'][key[0]];g=[set() for _ in range(21)]
 def add(g,u,v):g[u].add(v);g[v].add(u)
 for u,v in cover['F_edges']+source[key]:add(g,u,v)
 for s,hosts in enumerate(rep['singleton_hosts'],7):
  for e in hosts:add(g,s,e)
 allowed={(h,d) for h in range(7) for d in range(7) if not g[14+h]&g[7+d] and 7+d not in g[14+h]}
 pairings={p for p in itertools.permutations(range(7)) if all((h,d) in allowed for h,d in enumerate(p))};assert pairings==set(map(tuple,r['pairings'])) and len(pairings)==len(r['pairings'])
 grouped=collections.defaultdict(set)
 for pairing,hosts in r['solutions']:
  p=tuple(pairing);hs=tuple(hosts);assert p in pairings and hs not in grouped[p];grouped[p].add(hs)
 total=0
 for p in pairings:
  hc={14+h:h for h in range(7)};hc.update({7+d:h for h,d in enumerate(p)});opts=[]
  for e in range(7):
   present=[hc[s] for s in g[e] if s>=7];assert len(present)==len(set(present))==3
   missing=set(range(7))-set(present);edges=[q for q in K if set(q)<=missing]
   opts.append([sum(1<<ki[q] for q in match) for match in itertools.combinations(edges,2) if len(set(match[0])|set(match[1]))==4])
  # Independent forward products on even empties then odd empties.
  order=[0,2,4,6,1,3,5];frontier=[(0,(0,)*7)]
  for e in order:
   nxt=[]
   for used,chosen in frontier:
    for m in opts[e]:
     if not used&m:nxt.append((used|m,chosen[:e]+(m,)+chosen[e+1:]))
   frontier=nxt
  expected={chosen for used,chosen in frontier};assert len(expected)==len(frontier) and expected==grouped[p];total+=len(expected)
 # Full49 direct test of first/last solution per E/S graph, independently numbered.
 for p,hs in (r['solutions'][:1]+r['solutions'][-1:]):
  full=[set(ns) for ns in g]+[set() for _ in range(28)]
  for h,d in enumerate(p):add(full,21+h,14+h);add(full,21+h,7+d)
  for i,(a,b) in enumerate(K):add(full,28+i,21+a);add(full,28+i,21+b)
  for e,m in enumerate(hs):
   for i in range(21):
    if m>>i&1:add(full,e,28+i)
  assert all(len(full[h])==8 for h in range(21,28)) and all(len(full[e])==7 for e in range(7))
  assert all(len(full[e]&full[h])==1 for e in range(7) for h in range(21,28))
  assert all(len(full[u]&full[v])<=1 for u in range(49) for v in range(u));direct+=1
 assert total==len(r['solutions']);out.append(dict(source_index=key[0],singleton_index=key[1],pairings=len(pairings),solutions=total))
assert seen==set(source)
result=dict(status='PASS',cases=len(out),pairings=sum(r['pairings'] for r in out),solutions=sum(r['solutions'] for r in out),direct_graph_checks=direct,pins=len(pins),seconds=time.monotonic()-start,results=out);(P/'results.json').write_text(json.dumps(result,indent=2)+'\n');print({k:v for k,v in result.items() if k!='results'})
