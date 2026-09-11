import pathlib,json,gzip,time,itertools,collections
P=pathlib.Path(__file__).parent
data=json.loads((P/'row-results.json').read_text());cover=json.loads((P/'results.json').read_text())
source=[(r['index'],r) for r in data['results'] if r['status']=='COMPLETE' and not r['negative']];out=[];start=time.monotonic();deadline=start+60
for i,r in source:
 if time.monotonic()>deadline:break
 g={u:sum(1<<x for x in h) for u,h in enumerate(cover['representatives'][i]['singleton_hosts'],7)};vertices=list(range(7,21));rows={u:[sum(1<<v for v in row) for row in r['rows'][str(u)]] for u in vertices};nodes=0;solutions=[];support={}
 def tick():
  global nodes
  nodes+=1
  if nodes>100000 or time.monotonic()>deadline:raise TimeoutError
 def bitindices(mask):
  while mask:
   b=mask&-mask;yield b.bit_length()-1;mask-=b
 def search(domains):
  tick();changed=True
  while changed:
   changed=False
   for u,v in itertools.permutations(vertices,2):
    bad=0
    for a in bitindices(domains[u]):
     tick()
     if not support[u,a,v]&domains[v]:bad|=1<<a
    if bad:
     domains[u]&=~bad;changed=True
     if domains[u]==0:return
  options=[(m.bit_count(),u) for u,m in domains.items() if m.bit_count()>1]
  if not options:
   edges=[]
   for u in vertices:
    mask=rows[u][next(bitindices(domains[u]))]
    edges.extend([u,v] for v in vertices if u<v and mask>>v&1)
   assert len(edges)==14;solutions.append(edges);return
  _,u=min(options)
  for a in bitindices(domains[u]):
   child=dict(domains);child[u]=1<<a;search(child)
 try:
  for u,v in itertools.permutations(vertices,2):
   for a,am in enumerate(rows[u]):
    compatible=0
    for b,bm in enumerate(rows[v]):
     tick()
     if ((am>>v)&1)==((bm>>u)&1) and ((g[u]|am)&(g[v]|bm)).bit_count()<=1:compatible|=1<<b
    support[u,a,v]=compatible
  search({u:(1<<len(rows[u]))-1 for u in vertices});status='COMPLETE'
 except TimeoutError:status='UNKNOWN'
 assert len({tuple(map(tuple,s)) for s in solutions})==len(solutions)
 out.append(dict(source_index=i,status=status,nodes=nodes,solutions=solutions,count=len(solutions)))

summary=dict(total=len(source),visited=len(out),unvisited=len(source)-len(out),counts=dict(collections.Counter(r['status'] for r in out)),solutions=sum(r['count'] for r in out),seconds=time.monotonic()-start,scope='Necessary E/S projection over 202 X classes. COMPLETE counts labelled S extensions only; high and pair vertices absent. UNKNOWN/unvisited preserved.')
(P/'completion-results.json').write_text(json.dumps(dict(summary=summary,results=out),indent=2)+'\n');print(summary)
