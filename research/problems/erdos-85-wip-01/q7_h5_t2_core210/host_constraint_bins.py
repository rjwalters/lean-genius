"""Independent heavy-first assignment into interchangeable singleton bins."""
import time
masks=[7,25,10,18,12,20]+[0]*12
caps=[6,5,5,5,5]
def feasible(G,deadline):
 for c in range(5):
  required=[v for v in range(5,23) if not G[v]&G[c]]
  required.sort(key=lambda v:(-masks[v-5].bit_count(),v))
  bins=[];weights=[];failed=set()
  def fill(i):
   if time.monotonic()>deadline:raise TimeoutError
   if i==len(required):return True
   state=(i,tuple(sorted(tuple(b) for b in bins)))
   if state in failed:return False
   v=required[i];w=masks[v-5].bit_count()
   for j,b in enumerate(bins):
    total=weights[j]+w
    if total>5 or len(b)+1>1+total or any(G[v]&G[u] for u in b):continue
    b.append(v);weights[j]+=w
    if fill(i+1):return True
    weights[j]-=w;b.pop()
   if len(bins)<caps[c]:
    bins.append([v]);weights.append(w)
    if fill(i+1):return True
    bins.pop();weights.pop()
   failed.add(state);return False
  if not fill(0):return False
 return True
