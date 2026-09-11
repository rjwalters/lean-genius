import pathlib,json,itertools,time,collections,hashlib,gzip
P=pathlib.Path(__file__).parent;S=P.parent/'h7-a7-empty-first/results.json';source=json.loads(S.read_text());hi=range(7);K=list(itertools.combinations(hi,2));Fcases=[{tuple(sorted((i,(i+1)%7))) for i in hi},{(0,1),(0,2),(1,2),(3,4),(3,5),(4,5),(5,6)}];singletons=list(range(7,21));E=set(range(42,49));results=[];start=time.monotonic();deadline=start+60

def check(g):
 nodes=0;domains={};initial={};events=[];stage='ROWS'
 def tick():
  nonlocal nodes
  nodes+=1
  if nodes>100000 or time.monotonic()>deadline:raise TimeoutError
 def compatible(u,a,v,b):
  tick()
  return (v in a)==(u in b) and len((g[u]|a)&(g[v]|b))<=1
 try:
  for u in singletons:
   e=len(g[u]&E);need=5-2*e;assert e in [1,2] and need in [1,3]
   options=[v for v in singletons if v!=u and not(g[u]&g[v]&set(hi)) and all(not g[v]&g[w] for w in g[u])]
   rows=[]
   for selected in itertools.combinations(options,need):
    tick()
    if all(not g[v]&g[w] for v,w in itertools.combinations(selected,2)):rows.append(set(selected))
   initial[u]=[sorted(row) for row in rows];domains[u]=rows
   if not rows:return dict(status='LOCAL_NEGATIVE',vertex=u,nodes=nodes,initial=initial,events=events)
  stage='ARC';changed=True
  while changed:
   changed=False
   for u,v in itertools.permutations(singletons,2):
    removed=[a for a in domains[u] if not any(compatible(u,a,v,b) for b in domains[v])]
    if removed:
     domains[u]=[a for a in domains[u] if a not in removed];events.append(dict(vertex=u,against=v,removed=[sorted(a) for a in removed]));changed=True
     if not domains[u]:return dict(status='ARC_NEGATIVE',vertex=u,nodes=nodes,initial=initial,events=events)
  return dict(status='ARC_CONSISTENT',nodes=nodes,initial=initial,events=events,remaining={u:[sorted(a) for a in rows] for u,rows in domains.items()})
 except TimeoutError:return dict(status='UNKNOWN',stage=stage,nodes=nodes,initial=initial,events=events)

for fixture_index,fixture in enumerate(source['fixtures']):
 F=Fcases[fixture['F_case']];fg=[set() for _ in hi]
 for x,y in F:fg[x].add(y);fg[y].add(x)
 phi={tuple(e):x for e,x in fixture['phi']};unused=list(map(set,fixture['unused']));count=0
 for choices in itertools.product(*[list(itertools.combinations(sorted(u),2)) for u in unused]):
  if len(set(choices))!=7 or any(fg[x]&fg[y] for x,y in choices):continue
  if time.monotonic()>deadline:break
  g=[set() for _ in range(49)]
  def edge(u,v):g[u].add(v);g[v].add(u)
  for i in hi:edge(i,7+2*i);edge(i,8+2*i)
  for k,(i,j) in enumerate(K):
   edge(i,21+k);edge(j,21+k)
   if (i,j) in phi:edge(21+k,42+phi[i,j])
  for x,y in F:edge(42+x,42+y)
  for i,pair in enumerate(choices):
   for x in pair:edge(7+2*i,42+x)
   edge(8+2*i,42+next(iter(unused[i]-set(pair))))
  assert all(len(g[u]&g[v])<=1 for u in range(49) for v in range(u))
  assert all(len(g[i])==8 for i in hi) and all(len(g[e])==7 for e in E)
  assert all(not g[u]&set(singletons) for u in singletons)
  result=check(g);result.update(fixture_index=fixture_index,choices=[list(p) for p in choices],adjacency=[sorted(ns) for ns in g]);results.append(result);count+=1
 print(fixture_index,count,dict(collections.Counter(r['status'] for r in results if r['fixture_index']==fixture_index)),flush=True)
summary=dict(total_fixed_partials=117,visited=len(results),unvisited=117-len(results),counts=dict(collections.Counter(r['status'] for r in results)),nodes=sum(r['nodes'] for r in results),seconds=time.monotonic()-start,source_sha256=hashlib.sha256(S.read_bytes()).hexdigest(),scope='Only117fixedE-first partials from twofixed properQcolourings; not an R/F class or H7 exclusion. UNKNOWN and unvisited remainopen.')
with gzip.open(P/'results.json.gz','wt') as f:json.dump(dict(summary=summary,results=results),f)
(P/'summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(summary)
