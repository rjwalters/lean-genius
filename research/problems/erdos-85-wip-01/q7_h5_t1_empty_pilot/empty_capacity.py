"""Necessary empty-neighbour multicover and empty-degree capacity filter."""
import itertools

def feasible(graph,tick):
 support={v:graph[v]&set(range(5)) for v in range(5,36)}
 demand={v:7-len(graph[v]) for v in support};domains=[]
 def extend(left,chosen):
  if not left:domains.append(set(chosen));return
  c=min(left)
  for v in support:
   if demand[v]>0 and c in support[v] and support[v]<=left and all(not(graph[v]&graph[w]) for w in chosen):extend(left-support[v],chosen+[v])
 extend(set(range(5)),[])
 pairs=[set(itertools.combinations(sorted(d),2)) for d in domains]
 def cover(chosen,available,rem):
  if not tick():return False
  if not any(rem.values()):
   if len(chosen)!=13:return False
   g=[s.copy() for s in graph]
   for k,d in enumerate(chosen):
    for v in domains[d]:g[36+k].add(v);g[v].add(36+k)
   for v in range(36,49):
    partners=[w for w in range(36,49) if v!=w and not any(g[w]&g[x] for x in g[v])]
    if len(partners)<7-len(g[v]):return False
   return True
  if len(chosen)>=13:return False
  valid=[k for k in available if all(rem[v]>0 for v in domains[k])];options=[]
  for v,n in rem.items():
   if n:
    choices=[k for k in valid if v in domains[k]]
    if len(choices)<n:return False
    options.append((len(choices),v,choices))
  _,v,choices=min(options)
  for block in itertools.combinations(choices,rem[v]):
   if len(chosen)+len(block)>13:continue
   used=set();r=rem.copy();ok=True
   for k in block:
    if used & pairs[k]:ok=False;break
    used |= pairs[k]
    for w in domains[k]:
     r[w]-=1
     if r[w]<0:ok=False
   if not ok:continue
   nxt=[k for k in valid if k not in block and not(pairs[k]&used) and v not in domains[k]]
   if cover(chosen+list(block),nxt,r):return True
   if not tick():return False
  return False
 return cover([],list(range(len(domains))),demand)
