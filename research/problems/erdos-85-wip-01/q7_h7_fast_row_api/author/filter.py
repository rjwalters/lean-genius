"""Complete local rows plus necessary pairwise consistency; no branching."""
import time,itertools

def check(adjacency, *, max_nodes=100000, deadline=None):
 g=list(map(set,adjacency));high=set(range(7));hosts=g[0];outside=sorted(set(range(7,49))-hosts)
 assert len(g)==49 and len(hosts)==8 and len(outside)==34
 assert all(u!=v and u in g[v] for u in range(49) for v in g[u])
 assert all(len(g[c])==8 and not g[c]&high for c in high)
 assert all(len(g[u]&g[v])<=1 for u in range(49) for v in range(u))
 assert all(len(g[h])==7 and len(g[h]&hosts)==1 for h in hosts)
 assert all(len(g[u]&hosts)==1 and not g[u]&set(outside) for u in outside)
 host={v:next(iter(g[v]&hosts)) for v in outside};mask={v:sum(1<<c for c in g[v]&high) for v in outside}
 nodes=0;initial={};events=[];domains={};stage='GENERATION'
 def tick():
  nonlocal nodes
  nodes+=1
  if nodes>max_nodes or (deadline is not None and time.monotonic()>deadline):raise TimeoutError
 common_limit={(u,v):1-len(g[u]&g[v]) for u in outside for v in outside if u!=v}
 def compatible(u,a,v,b):
  tick()
  return ((a>>v)&1)==((b>>u)&1) and (a&b).bit_count()<=common_limit[u,v]
 try:
  for u in outside:
   missing=127
   for v in g[u]:
    if v>=7:missing&=~sum(1<<c for c in g[v]&high)
   need=7-len(g[u]);options={}
   for v in outside:
    if u==v or mask[v]&missing!=mask[v] or any(g[v]&g[w] for w in g[u]):continue
    options.setdefault(host[v],[]).append(v)
   gs=sorted(options,key=lambda h:(len(options[h]),h));answers=[]
   def dfs(i,left,n,selected):
    tick()
    if n==0:
     if left==0:answers.append(sum(1<<v for v in selected))
     return
    if len(gs)-i<n:return
    if len(gs)-i>n:dfs(i+1,left,n,selected)
    for v in options[gs[i]]:
     if mask[v]&left==mask[v]:dfs(i+1,left^mask[v],n-1,selected+[v])
   dfs(0,missing,need,[]);initial[u]=answers
   if not answers:return dict(status='INFEASIBLE_LOCAL',nodes=nodes,initial=initial,events=[],empty_vertex=u)
  domains={u:list(a) for u,a in initial.items()};stage='ARC';changed=True
  while changed:
   changed=False
   for u,v in itertools.permutations(outside,2):
    removed=[a for a in domains[u] if not any(compatible(u,a,v,b) for b in domains[v])]
    if removed:
     bad=set(removed);domains[u]=[a for a in domains[u] if a not in bad];events.append(dict(vertex=u,against=v,removed=removed));changed=True
     if not domains[u]:return dict(status='INFEASIBLE_ARC',nodes=nodes,initial=initial,events=events,empty_vertex=u)
  return dict(status='ARC_CONSISTENT',nodes=nodes,initial=initial,events=events,remaining=domains)
 except TimeoutError:
  return dict(status='UNKNOWN',stage=stage,nodes=nodes,initial=initial,events=events)
