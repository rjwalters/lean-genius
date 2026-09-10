from pathlib import Path
import json,itertools,time,hashlib
from functools import lru_cache
src=Path('/Users/rwalters/lean-genius-q7-outside-first-20260910/core44-sharing-structure')
p=Path(__file__).parent
pins=json.loads((src/'sharing1-pins.json').read_text())
assert all(hashlib.sha256((src/f).read_bytes()).hexdigest()==h for f,h in pins.items())
cases=[r for r in json.loads((src/'branches.json').read_text())['results'] if r['shared']==1 and r['omitted'] in (7,11) and r['internal']==[] and r['af']==4 and r['bf']==2]
assert len(cases)==2
start=time.monotonic();out=[]
E=range(11,23);emask=sum(1<<e for e in E)
for case in cases:
 g=[sum(1<<v for v in ns) for ns in case['adjacency']]
 nodes=0;stars=0;hostcalls=0
 def tick():
  global nodes
  nodes+=1
  if nodes>100000 or time.monotonic()-start>60:raise TimeoutError
 def edge(a,b):g[a]|=1<<b;g[b]|=1<<a
 def remove(a,b):g[a]^=1<<b;g[b]^=1<<a
 def clean():return all((g[a]&g[b]).bit_count()<=1 for a,b in itertools.combinations(range(32),2))
 assert clean()
 weights=[(x&31).bit_count() for x in g]
 targets={e:2+sum(weights[h]-1 for h in range(5,11) if g[e]>>h&1) for e in E}
 def hosts():
  global hostcalls
  hostcalls+=1
  for c,cap in enumerate((3,4,3,4,3)):
   req=[v for v in range(5,32) if not g[v]&g[c]]
   n=len(req);groups=[[] for _ in req]
   def subsets(i,mask,w,d):
    tick()
    if mask and d<=w+1:
     for j in range(n):
      if mask>>j&1:groups[j].append(mask)
    for j in range(i,n):
     v=req[j]
     if w+weights[v]<=5 and all(not g[v]&g[req[k]] for k in range(n) if mask>>k&1):
      subsets(j+1,mask|1<<j,w+weights[v],d+1)
   subsets(0,0,0,0)
   @lru_cache(None)
   def partition(left,k):
    tick()
    if not left:return True
    if not k:return False
    j=(left&-left).bit_length()-1
    return any(partition(left^s,k-1) for s in groups[j] if s&left==s)
   if not partition((1<<n)-1,cap):return False
  return True
 def legal(a,b):
  if a==b or g[a]>>b&1:return False
  edge(a,b);ok=clean();remove(a,b);return ok
 def fill():
  tick()
  if not hosts():return False
  rem={e:targets[e]-(g[e]&emask).bit_count() for e in E}
  if any(n<0 for n in rem.values()):return False
  active=[e for e,n in rem.items() if n]
  if not active:return True
  domains={e:[v for v in active if legal(e,v)] for e in active}
  if any(len(domains[e])<rem[e] for e in active):return False
  e=min(active,key=lambda e:len(domains[e])-rem[e])
  for block in itertools.combinations(domains[e],rem[e]):
   for v in block:edge(e,v)
   if clean() and fill():return True
   for v in block:remove(e,v)
  return False
 def star(k):
  global stars
  tick()
  if k==5:stars+=1;return fill()
  v=27+k
  for block in itertools.combinations(E,3 if k==1 else 2):
   for e in block:edge(v,e)
   if clean() and star(k+1):return True
   for e in block:remove(v,e)
  return False
 try:status='FOUND' if star(0) else 'EXHAUSTED'
 except TimeoutError:status='UNKNOWN'
 out.append(dict(omitted=case['omitted'],status=status,nodes=nodes,complete_stars=stars,host_calls=hostcalls))
 print(out[-1],flush=True)
assert all(hashlib.sha256((src/f).read_bytes()).hexdigest()==h for f,h in pins.items())
(p/'results.json').write_text(json.dumps(dict(results=out,seconds=time.monotonic()-start,pins_verified=pins,method='Independent static F-star order; full pairwise common-neighbour checks; first-guest subset partitions at every empty-graph node; no author imports.'),indent=2)+'\n')
