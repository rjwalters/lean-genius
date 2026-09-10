"""Independent descending-weight guest assignment to interchangeable singleton bins."""
import time
def check(adj,deadline,node_cap=100000):
 g=list(map(set,adj));weight={v:len(g[v]&set(range(5))) for v in range(5,32)};nodes=0
 try:
  for c,capacity in enumerate([3,4,3,4,3]):
   req=sorted([v for v in weight if not g[v]&g[c]],key=lambda v:(-weight[v],v));bins=[];failed=set()
   def fill(i):
    nonlocal nodes
    nodes+=1
    if nodes>node_cap or time.monotonic()>deadline:raise TimeoutError
    if i==len(req):return True
    state=(i,tuple(sorted(tuple(b) for b in bins)))
    if state in failed:return False
    v=req[i]
    for b in bins:
     w=sum(weight[u] for u in b)+weight[v]
     if w>5 or len(b)+1>1+w or any(g[v]&g[u] for u in b):continue
     b.append(v)
     if fill(i+1):return True
     b.pop()
    if len(bins)<capacity:
     bins.append([v])
     if fill(i+1):return True
     bins.pop()
    failed.add(state);return False
   if not fill(0):return dict(status='EXHAUSTED',nodes=nodes,colour=c)
  return dict(status='LOCAL_PARTITIONS',nodes=nodes)
 except TimeoutError:return dict(status='CAPPED',nodes=nodes)
