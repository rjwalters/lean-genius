import pathlib,json,gzip,itertools,time
P=pathlib.Path(__file__).parent
with gzip.open(P/'results.json.gz','rt') as f:data=json.load(f)
completion=json.loads((P/'completion-results.json').read_text());V=list(range(7,21));H=set(range(7));E=set(range(42,49));rowcount=failures=0
for r in data['results']:
 g=list(map(set,r['adjacency']));domains={}
 for key,raw in r['initial'].items():
  u=int(key);need=5-2*len(g[u]&E);options=[v for v in V if v!=u and not g[v]&g[u]&H];generated=[]
  for selected in itertools.combinations(options,need):
   ns=g[u]|set(selected)
   if all(not ((g[v]-{u})&(g[w]-{u})) for v,w in itertools.combinations(ns,2)):generated.append(frozenset(selected))
  assert set(generated)=={frozenset(row) for row in raw};domains[u]=set(generated);rowcount+=len(generated)
 for e in r['events']:
  u,v=e['vertex'],e['against'];assert u!=v
  removed={frozenset(a) for a in e['removed']};assert removed<=domains[u]
  for a in removed:
   for b in domains[v]:
    assert ((v in a)!=(u in b)) or len((g[u]|a)&(g[v]|b))>1;failures+=1
  domains[u]-=removed
 if r['status']=='ARC_NEGATIVE':assert not domains[r['vertex']]
 elif r['status']=='ARC_CONSISTENT':assert domains=={int(u):{frozenset(a) for a in rows} for u,rows in r['remaining'].items()}
 else:raise AssertionError(r['status'])
# Independent whole-vertex star completion; no row compatibility tables.
start=time.monotonic();deadline=start+60;out=[]
for result in completion['results']:
 r=data['results'][result['source_index']];base=list(map(set,r['adjacency']));target={u:5-2*len(base[u]&E) for u in V};nodes=0;answers=set()
 def clean(g):return all(len(g[u]&g[v])<=1 for u in range(49) for v in range(u))
 def dfs(g):
  nonlocal_dummy=None
  global nodes
  nodes+=1
  if nodes>100000 or time.monotonic()>deadline:raise TimeoutError
  unfinished=[u for u in V if len(g[u]&set(V))<target[u]]
  if not unfinished:
   answers.add(tuple((u,v) for u in V for v in V if u<v and v in g[u]));return
  choices=[]
  for u in unfinished:
   need=target[u]-len(g[u]&set(V));opts=[]
   for v in unfinished:
    if u==v or v in g[u] or g[u]&g[v]&H:continue
    if all(not ((g[v]-{u})&(g[w]-{u})) for w in g[u]):opts.append(v)
   if len(opts)<need:return
   choices.append((len(opts),-need,u,need,opts))
  _,_,u,need,opts=min(choices)
  for selected in itertools.combinations(opts,need):
   q=[ns.copy() for ns in g]
   for v in selected:q[u].add(v);q[v].add(u)
   if clean(q):dfs(q)
 try:dfs(base);status='COMPLETE'
 except TimeoutError:status='UNKNOWN'
 if status=='COMPLETE':assert answers=={tuple(map(tuple,s)) for s in result['solutions']}
 out.append(dict(source_index=result['source_index'],status=status,nodes=nodes,solutions=len(answers)))
 if status=='UNKNOWN':break
assert len(out)==25 and all(r['status']=='COMPLETE' for r in out)
verification=dict(status='PASS',all_initial_rows_independently_regenerated=rowcount,failed_supports_replayed=failures,whole_star_completion=out,total_singleton_graphs=sum(r['solutions'] for r in out),seconds=time.monotonic()-start,scope='Only117fixedE-first partials; exact33singleton extensions across18surviving bases, no wholeR/F or fullH7exclusion.')
(P/'verification.json').write_text(json.dumps(verification,indent=2)+'\n');print({k:v for k,v in verification.items() if k!='whole_star_completion'})
