"""Enumerate remaining heavy edges after complete colour0 labelling."""
import pathlib,json,itertools,time
P=pathlib.Path(__file__).parent;deadline=time.monotonic()+60;out=[]
for branch in json.loads((P/'empty-slot-results.json').read_text())['results']:
 nodes=0;heavy_leaves=0;survivors=[]
 for index,partial in enumerate(branch['survivors']):
  g=list(map(set,partial['adjacency']));mask=[sum(1<<h for h in ns if h<5) for ns in g]
  def missing(v):
   covered=0
   for w in g[v]:
    if w>=5:covered|=mask[w]
   return 31^covered
  def legal(u,v):return u!=v and v not in g[u] and len(g[u])<7 and len(g[v])<7 and mask[v]&missing(u)==mask[v] and mask[u]&missing(v)==mask[u] and all(not g[v]&g[w] for w in g[u])
  def necessary():
   for u in range(5,49):
    if len(g[u])==7:continue
    opts=[v for v in range(5,49) if legal(u,v)]
    if len(opts)<7-len(g[u]):return False
    covered=0
    for v in opts:covered|=mask[v]
    if covered&missing(u)!=missing(u):return False
   return True
  def dfs(todo,added):
   global nodes,heavy_leaves
   nodes+=1
   if nodes>100000 or time.monotonic()>deadline:raise TimeoutError
   if not todo:
    heavy_leaves+=1
    if necessary():survivors.append(dict(empty_index=index,edges=added))
    return
   opts=[]
   for u,c in todo:
    choices=[v for v in range(35,49) if mask[v]==1<<c and legal(u,v)]
    opts.append((len(choices),u,c,choices))
   _,u,c,choices=min(opts)
   for v in choices:
    g[u].add(v);g[v].add(u)
    dfs([r for r in todo if r!=(u,c)],added+[(u,v)])
    g[u].remove(v);g[v].remove(u)
  try:dfs([(7,1),(8,3),(8,4),(9,3),(9,4)],[])
  except TimeoutError:
   out.append(dict(omitted=branch['omitted'],internal=branch['internal'],status='CAPPED',nodes=nodes,heavy_leaves=heavy_leaves,survivors=survivors));break
 else:
  out.append(dict(omitted=branch['omitted'],internal=branch['internal'],status='EXHAUSTED_DOMAIN',nodes=nodes,heavy_leaves=heavy_leaves,survivors=survivors))
 print({k:v for k,v in out[-1].items() if k!='survivors'},'survivors',len(out[-1]['survivors']),flush=True)
(P/'heavy-slot-results.json').write_text(json.dumps(dict(results=out,scope='Conditional colour0/heavy edge domain and necessary local edge availability only. Positive partials need remaining singleton and empty edges.'),indent=2)+'\n')
