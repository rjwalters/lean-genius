from pathlib import Path
import json,itertools,time,collections
P=Path(__file__).parent;cover=json.loads((P/'cover-results.json').read_text());completed=json.loads((P/'completion-results.json').read_text());records={(r['F_index'],r['X_index']):r for r in completed['results']};start=time.monotonic();out=[]
for F in cover['cases']:
 for xi,X in enumerate(F['representatives']):
  base=[set() for _ in range(21)]
  def add(g,u,v):g[u].add(v);g[v].add(u)
  for x,y in F['F_edges']:add(base,x,y)
  for u,hosts in enumerate(X['singleton_hosts'],7):
   for x in hosts:add(base,u,x)
  targets={u:5-len(base[u]) for u in range(7,21)};g=[set(ns) for ns in base];solutions=set();nodes=0
  def c4free():
   seen=set()
   for ns in g:
    for pair in itertools.combinations(sorted(ns),2):
     if pair in seen:return False
     seen.add(pair)
   return True
  def visit(u):
   nonlocal_dummy=None
   global nodes
   nodes+=1
   if nodes>100000 or time.monotonic()-start>60:raise TimeoutError
   if u==21:
    solutions.add(tuple((v,w) for v in range(7,21) for w in sorted(g[v]) if v<w));return
   need=targets[u]-len(g[u])
   if need<0:return
   candidates=[v for v in range(u+1,21) if len(g[v])<targets[v]]
   for choice in itertools.combinations(candidates,need):
    for v in choice:add(g,u,v)
    if c4free():visit(u+1)
    for v in choice:g[u].remove(v);g[v].remove(u)
  visit(7)
  r=records[F['F_index'],xi];assert r['status']=='COMPLETE' and solutions=={tuple(map(tuple,s)) for s in r['solutions']}
  out.append({'F_index':F['F_index'],'X_index':xi,'nodes':nodes,'solutions':len(solutions)})
r={'status':'PASS','cases':len(out),'solutions':sum(r['solutions'] for r in out),'positive':sum(bool(r['solutions']) for r in out),'nodes':sum(r['nodes'] for r in out),'max_nodes':max(r['nodes'] for r in out),'seconds':time.monotonic()-start,'results':out,'scope':'Independent fixedascending-vertex wholegraph completion with length-two path collision checks; all a6 E/S solution sets. No high/P assignment.'};(P/'verification.json').write_text(json.dumps(r,indent=2)+'\n');print({k:v for k,v in r.items() if k!='results'})
