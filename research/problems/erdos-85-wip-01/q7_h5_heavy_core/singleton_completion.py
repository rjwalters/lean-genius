"""Bounded T2 completion of singleton colour incidences, before empty edges."""
import itertools,json,time,hashlib
from pathlib import Path
from host_pilot import hostings

source=json.loads(Path('core-t2.json').read_text());masks=source['masks'];n=len(masks)
capacities=[4+sum(bool(m>>c&1) for m in masks if m.bit_count()==3) for c in range(5)]
supports=masks+[1<<c for c in range(5) for _ in range(capacities[c])];supports+=[0]*(44-len(supports))
S=list(range(5+n,5+n+sum(capacities)));col={v:supports[v-5].bit_length()-1 for v in S}
start=time.monotonic();deadline=start+60;results=[]
for core in source['canonical_cores']:
 if time.monotonic()>deadline:break
 adj=[set() for _ in masks]
 for i,(u,v) in enumerate(itertools.combinations(range(n),2)):
  if core>>i&1:adj[u].add(v);adj[v].add(u)
 options=[hostings([u for u in range(n) if not any(masks[v]>>c&1 for v in adj[u])],masks,adj,capacities[c]) for c in range(5)]
 nodes=0;hosts_tried=0;host_candidates=0;found=None;capped=False
 def search(graph,needs):
  global nodes
  nodes+=1
  if nodes>100000 or time.monotonic()>deadline:raise TimeoutError
  def allowed(u,v):
   if graph[u]>>v&1:return False
   for a,b in [(u,v),(v,u)]:
    neighbors=graph[a]
    while neighbors:
     bit=neighbors&-neighbors;w=bit.bit_length()-1;neighbors-=bit
     if graph[b]&graph[w]:return False
   return True
  best=None
  for u in S:
   missing=needs[u]
   while missing:
    bit=missing&-missing;c=bit.bit_length()-1;missing-=bit
    cand=[v for v in S if v!=u and col[v]==c and needs[v]>>col[u]&1 and allowed(u,v)]
    if not cand:return None
    if best is None or len(cand)<len(best[2]):best=(u,c,cand)
  if best is None:return list(graph)
  u,c,cand=best
  for v in cand:
   graph[u]|=1<<v;graph[v]|=1<<u;needs[u]^=1<<c;needs[v]^=1<<col[u]
   result=search(graph,needs)
   if result is not None:return result
   graph[u]^=1<<v;graph[v]^=1<<u;needs[u]^=1<<c;needs[v]^=1<<col[u]
  return None
 try:
  for groups in itertools.product(*options):
   paired=[g for colour in groups for g in colour if len(g)==2]
   if len(set(paired))!=len(paired):continue
   host_candidates+=1;graph=[0]*49
   def edge(u,v):graph[u]|=1<<v;graph[v]|=1<<u
   for v,mask in enumerate(supports,5):
    for c in range(5):
     if mask>>c&1:edge(c,v)
   for u in range(n):
    for v in adj[u]:edge(u+5,v+5)
   offset=5+n
   for c,bins in enumerate(groups):
    for i,bin in enumerate(bins):
     for v in bin:edge(offset+i,5+v)
    offset+=capacities[c]
   needs=[0]*49
   for v in S:
    for c in range(5):
     if not graph[v]&graph[c]:needs[v]|=1<<c
   hosts_tried+=1;solution=search(graph,needs)
   if solution is not None:found=dict(hosts=groups,adjacency=solution);break
 except TimeoutError:capped=True
 status='PARTIAL_WITNESS' if found else ('CAPPED' if capped else 'EXCLUDED_SINGLETON_COMPLETION')
 results.append(dict(core=core,status=status,nodes=nodes,hosts_tried=hosts_tried,host_candidates=host_candidates,witness=found))
 print(core,status,nodes,hosts_tried,flush=True)
result=dict(source_sha256=hashlib.sha256(Path('core-t2.json').read_bytes()).hexdigest(),results=results,unvisited=13-len(results),seconds=time.monotonic()-start,per_core_node_cap=100000,wall_cap_seconds=60,scope='All nonempty-support BC rows completed for positive witnesses. Empty-incident edges absent; no full graph or sector exclusion.')
Path('singleton-t2.json').write_text(json.dumps(result,indent=2)+'\n')
