import itertools,json,time
from pathlib import Path
p=Path(__file__).parent;start=time.monotonic();out=[]
for row in json.loads((p/'patterns.json').read_text()):
 G=[set() for _ in range(27)]
 for u,v in row['edges']:G[u].add(v);G[v].add(u)
 target={15+e:(4 if e==0 else 3 if e in [1,2,3,4,5,8] else 2) for e in range(12)};rem={v:target[v]-len(G[v]&set(target)) for v in target};nodes=0
 def dfs():
  global nodes
  nodes+=1
  if nodes>100000 or time.monotonic()-start>60:raise TimeoutError
  active=[v for v in rem if rem[v]]
  if not active:return True
  opts={v:[w for w in active if w!=v and w not in G[v] and all(not G[w]&G[x] for x in G[v])] for v in active}
  if any(len(opts[v])<rem[v] for v in active):return False
  v=min(active,key=lambda v:len(opts[v])-rem[v]);need=rem[v]
  for group in itertools.combinations(opts[v],need):
   if any(G[a]&G[b] for a,b in itertools.combinations(group,2)):continue
   rem[v]=0
   for w in group:G[v].add(w);G[w].add(v);rem[w]-=1
   if dfs():return True
   for w in group:G[v].remove(w);G[w].remove(v);rem[w]+=1
   rem[v]=need
  return False
 try:
  found=dfs();status='PROJECTED_WITNESS' if found else 'EXHAUSTED'
 except TimeoutError:found=False;status='UNKNOWN'
 out.append(dict(omitted=row['omitted'],status=status,nodes=nodes,edges=[(u,v) for u in range(27) for v in G[u] if u<v] if found else None));print({k:v for k,v in out[-1].items() if k!='edges'},flush=True)
 if time.monotonic()-start>60:break
(p/'empty-results.json').write_text(json.dumps(dict(results=out,seconds=time.monotonic()-start,node_cap=100000,wall_cap=60,scope='Necessary E graph completion for four proposed universal core44 patterns; normalization argument pending independent review'),indent=2)+'\n')
