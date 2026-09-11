import pathlib,json,itertools,hashlib,sqlite3,time,collections
P=pathlib.Path(__file__).parent;A=pathlib.Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3/h7-a6-empty-singleton-projection');read=lambda p:json.loads(p.read_text());pins=read(A/'pins.json')
for f,h in pins.items():assert hashlib.sha256((A/f).read_bytes()).hexdigest()==h
c=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True);c.row_factory=sqlite3.Row
for old in read(A/'premises.json'):
 live=dict(c.execute('select * from review_requests where id=?',(old['id'],)).fetchone())
 for r in [old,live]:
  if isinstance(r['refs'],str):r['refs']=json.loads(r['refs'])
  r.pop('expired',None)
 assert old==live and live['resolution'].startswith('PASS')
K=list(itertools.combinations(range(7),2));ki={e:i for i,e in enumerate(K)};raw=set();start=time.monotonic()
for es in itertools.combinations(list(reversed(K)),6):
 g=[set() for _ in range(7)]
 for u,v in es:g[u].add(v);g[v].add(u)
 if max(map(len,g))>3:continue
 paths=[pair for ns in g for pair in itertools.combinations(sorted(ns),2)]
 if len(paths)==len(set(paths)):raw.add(sum(1<<ki[e] for e in es))
cover=read(A/'cover-results.json');done=read(A/'completion-results.json');records={(r['F_index'],r['X_index']):r for r in done['results']};perms=list(itertools.permutations(range(7)));seenF=set();bases=[];xtotal=0
for f in cover['cases']:
 F=set(map(tuple,f['F_edges']));orbit={sum(1<<ki[tuple(sorted((p[u],p[v])))] for u,v in F) for p in perms};assert orbit<=raw and not orbit&seenF and len(orbit)==f['F_orbit_size'];seenF|=orbit
 fg=[{v for v in range(7) if tuple(sorted((u,v))) in F} for u in range(7)];allowed=[e for e in K if not fg[e[0]]&fg[e[1]]];ix={e:i for i,e in enumerate(allowed)};Xraw=set()
 for absent in itertools.combinations(range(len(allowed)),len(allowed)-11):
  mask=((1<<len(allowed))-1)^sum(1<<e for e in absent)
  if all(sum(bool(mask>>j&1) for j,e in enumerate(allowed) if u in e)<=7-2*len(fg[u]) for u in range(7)):Xraw.add(mask)
 aut=[p for p in perms if {tuple(sorted((p[u],p[v]))) for u,v in F}==F];assert len(aut)==f['AutF_order'];seenX=set()
 for xi,x in enumerate(f['representatives']):
  orbit={sum(1<<ix[tuple(sorted((p[u],p[v])))] for u,v in x['X_edges']) for p in aut};assert orbit<=Xraw and not orbit&seenX and len(orbit)==x['orbit_size'];seenX|=orbit
  expected=[list(e) for e in x['X_edges']]
  for u in range(7):expected.extend([[u]]*(7-2*len(fg[u])-sum(u in e for e in x['X_edges'])))
  assert expected==x['singleton_hosts'];bases.append((f,xi,x))
 assert seenX==Xraw and len(Xraw)==f['raw_X'];xtotal+=len(Xraw)
assert seenF==raw and len(raw)==31332 and len(bases)==358 and xtotal==2192
cover_seconds=time.monotonic()-start;start=time.monotonic();out=[]
def bits(m):
 while m:
  b=m&-m;yield b.bit_length()-1;m-=b
for f,xi,x in bases:
 g=[0]*21
 def edge(u,v):g[u]|=1<<v;g[v]|=1<<u
 for u,v in f['F_edges']:edge(u,v)
 for u,hs in enumerate(x['singleton_hosts'],7):
  for e in hs:edge(u,e)
 target={u:5-g[u].bit_count() for u in range(7,21)};order=sorted(target,key=lambda u:(g[u].bit_count(),u));assert order[:3]==[18,19,20];solutions=set();nodes=0
 def visit(k):
  global nodes
  nodes+=1
  if nodes>100000 or time.monotonic()-start>60:raise TimeoutError
  if k==14:
   assert all(g[u].bit_count()==target[u] for u in target) and all((g[u]&g[v]).bit_count()<=1 for u in range(21) for v in range(u))
   solutions.add(tuple((u,v) for u in range(7,21) for v in bits(g[u]) if v>u));return
  u=order[k];need=target[u]-g[u].bit_count()
  if need<0:return
  candidates=[v for v in order[k+1:] if g[v].bit_count()<target[v] and not(g[u]>>v&1) and all(not(g[v]&g[w]&~(1<<u)) for w in bits(g[u]))]
  for choice in itertools.combinations(candidates,need):
   if any(g[v]&g[w]&~(1<<u) for v,w in itertools.combinations(choice,2)):continue
   old=g[u]
   for v in choice:edge(u,v)
   visit(k+1)
   for v in choice:g[v]^=1<<u
   g[u]=old
 visit(0);r=records[f['F_index'],xi];assert r['status']=='COMPLETE' and solutions=={tuple(map(tuple,s)) for s in r['solutions']};out.append(dict(F_index=f['F_index'],X_index=xi,nodes=nodes,solutions=len(solutions)))
r=dict(status='PASS',F_labelled=len(raw),F_orbits=len(cover['cases']),X_labelled=xtotal,X_orbits=len(bases),solutions=sum(x['solutions'] for x in out),positive=sum(x['solutions']>0 for x in out),max_nodes=max(x['nodes'] for x in out),nodes=sum(x['nodes'] for x in out),cover_seconds=cover_seconds,completion_seconds=time.monotonic()-start,pins=len(pins),results=out);(P/'results.json').write_text(json.dumps(r,indent=2)+'\n');print({k:v for k,v in r.items() if k!='results'})
