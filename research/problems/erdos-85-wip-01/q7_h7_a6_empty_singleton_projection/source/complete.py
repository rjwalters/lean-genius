from pathlib import Path
import json,itertools,math,time
P=Path(__file__).parent;source=json.loads((P/'cover-results.json').read_text());assert source['status']=='COMPLETE'
def bits(mask):
 while mask:
  b=mask&-mask;yield b.bit_length()-1;mask-=b
start=time.monotonic();deadline=start+60;records=[];stop=False
for F in source['cases']:
 for xi,X in enumerate(F['representatives']):
  if time.monotonic()>deadline:stop=True;break
  base=[0]*21
  def edge(g,u,v):g[u]|=1<<v;g[v]|=1<<u
  for x,y in F['F_edges']:edge(base,x,y)
  for u,hosts in enumerate(X['singleton_hosts'],7):
   for x in hosts:edge(base,u,x)
  target={u:5-base[u].bit_count() for u in range(7,21)};g=base[:];solutions=set();nodes=0
  def visit(unfixed):
   global nodes
   nodes+=1
   if nodes>100000 or time.monotonic()>deadline:raise TimeoutError
   if not unfixed:
    assert all(g[u].bit_count()==target[u] for u in target)
    assert all((g[u]&g[v]).bit_count()<=1 for u in range(21) for v in range(u))
    solutions.add(tuple((u,v) for u in range(7,21) for v in bits(g[u]) if v>u));return
   choices=[]
   for u in unfixed:
    need=target[u]-g[u].bit_count()
    if need<0:return
    candidates=[v for v in unfixed if v!=u and target[v]>g[v].bit_count() and not(g[u]>>v&1) and all(not(g[v]&g[w]) for w in bits(g[u]))]
    if need>len(candidates):return
    choices.append((math.comb(len(candidates),need),u,need,candidates))
   _,u,need,candidates=min(choices,key=lambda x:(x[0],-x[1]))
   for block in itertools.combinations(candidates,need):
    if any(g[v]&g[w] for v,w in itertools.combinations(block,2)):continue
    old=g[u]
    for v in block:edge(g,u,v)
    visit(tuple(v for v in unfixed if v!=u))
    for v in block:g[v]^=1<<u
    g[u]=old
  status='COMPLETE'
  try:visit(tuple(range(7,21)))
  except TimeoutError:status='UNKNOWN'
  records.append({'F_index':F['F_index'],'X_index':xi,'status':status,'nodes':nodes,'solutions':sorted(solutions)})
 if stop:break
r={'status':'COMPLETE' if len(records)==source['X_orbits_total'] and all(r['status']=='COMPLETE' for r in records) else 'UNKNOWN','cases':len(records),'unvisited':source['X_orbits_total']-len(records),'positive':sum(bool(r['solutions']) for r in records),'solutions':sum(len(r['solutions']) for r in records),'nodes':sum(r['nodes'] for r in records),'max_nodes':max(r['nodes'] for r in records),'results':records,'seconds':time.monotonic()-start,'scope':'One a6E/S singleton-edge completion pass,100krecursive states/Xcase60saggregate. UNKNOWNnotexcluded; no high/P/fullgraph completion or oldcappedhosttree retry.'};(P/'completion-results.json').write_text(json.dumps(r,indent=2)+'\n');print({k:v for k,v in r.items() if k!='results'})
