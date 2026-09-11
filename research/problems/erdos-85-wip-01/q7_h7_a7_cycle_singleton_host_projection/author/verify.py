import pathlib,json,itertools,time,collections
P=pathlib.Path(__file__).parent;cover=json.loads((P/'results.json').read_text());rows=json.loads((P/'row-results.json').read_text());completed=json.loads((P/'completion-results.json').read_text());start=time.monotonic();deadline=start+60;out=[];totalrows=0
for i,c in enumerate(cover['representatives']):
 base=[set() for _ in range(21)]
 def add(g,u,v):g[u].add(v);g[v].add(u)
 for x,y in cover['F_edges']:add(base,x,y)
 for u,h in enumerate(c['singleton_hosts'],7):
  for x in h:add(base,u,x)
 def c4free(g):
  seen=set()
  for ns in g:
   for pair in itertools.combinations(sorted(ns),2):
    if pair in seen:return False
    seen.add(pair)
  return True
 target={u:5-len(base[u]) for u in range(7,21)}
 for u in range(7,21):
  domain=[]
  for choice in itertools.combinations([v for v in range(7,21) if v!=u],target[u]-len(base[u])):
   g=[set(ns) for ns in base]
   for v in choice:add(g,u,v)
   if c4free(g):domain.append(list(choice))
  assert domain==rows['results'][i]['rows'][str(u)];totalrows+=len(domain)
 g=[set(ns) for ns in base];solutions=set();nodes=0
 def visit(u):
  global nodes
  nodes+=1
  if nodes>100000 or time.monotonic()>deadline:raise TimeoutError
  if u==21:
   solutions.add(tuple((v,w) for v in range(7,21) for w in sorted(g[v]) if v<w));return
  need=target[u]-len(g[u]);candidates=[v for v in range(u+1,21) if len(g[v])<target[v]]
  if need<0:return
  for choice in itertools.combinations(candidates,need):
   for v in choice:add(g,u,v)
   if c4free(g):visit(u+1)
   for v in choice:g[u].remove(v);g[v].remove(u)
 try:visit(7);status='COMPLETE'
 except TimeoutError:status='UNKNOWN'
 author=completed['results'][i];assert status=='COMPLETE' and author['status']=='COMPLETE'
 assert solutions=={tuple(map(tuple,s)) for s in author['solutions']}
 out.append(dict(index=i,status=status,nodes=nodes,solutions=len(solutions)))
r=dict(status='PASS',cases=len(out),rows=totalrows,solutions=sum(x['solutions'] for x in out),positive=sum(x['solutions']>0 for x in out),seconds=time.monotonic()-start,results=out)
(P/'verification.json').write_text(json.dumps(r,indent=2)+'\n');print({k:v for k,v in r.items() if k!='results'})
