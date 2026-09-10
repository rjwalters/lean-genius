from pathlib import Path
import json,itertools,time
p=Path(__file__).parent;start=time.monotonic();results=[]
def key(r):return (r['shared'],r['omitted'],tuple(map(tuple,r['internal'])),r['af'],r['bf'])
source=json.loads((p/'sharing-empty-results.json').read_text());negative=set()
for group in source['results']:
 for c in group['choices']:
  if c['status']=='EXHAUSTED':negative.add(key(dict(c,shared=group['shared'],omitted=group['omitted'])))
assert len(negative)==64
for case in json.loads((p/'branches.json').read_text())['results']:
 if key(case) not in negative:continue
 g=list(map(set,case['adjacency']));nodes=0;leaves=0
 def edge(a,b):g[a].add(b);g[b].add(a)
 def remove(a,b):g[a].remove(b);g[b].remove(a)
 def clean():return all(len(g[a]&g[b])<=1 for a,b in itertools.combinations(range(32),2))
 assert clean()
 targets={e:2+sum(len(g[h]&set(range(5)))-1 for h in g[e] if 5<=h<11) for e in range(11,23)}
 def tick():
  global nodes
  nodes+=1
  if nodes>100000 or time.monotonic()-start>60:raise TimeoutError
 def legal(a,b):
  if a==b or b in g[a]:return False
  edge(a,b);ok=clean();remove(a,b);return ok
 def fill():
  tick();rem={e:targets[e]-len(g[e]&set(range(11,23))) for e in range(11,23)}
  if any(n<0 for n in rem.values()):return False
  active=[e for e,n in rem.items() if n]
  if not active:return True
  cs={e:[v for v in active if legal(e,v)] for e in active}
  if any(len(cs[e])<rem[e] for e in active):return False
  e=min(active,key=lambda e:len(cs[e])-rem[e])
  for block in itertools.combinations(cs[e],rem[e]):
   for v in block:edge(e,v)
   if clean() and fill():return True
   for v in block:remove(e,v)
  return False
 def host(k):
  global leaves
  tick()
  if k==5:leaves+=1;return fill()
  v=27+k
  for block in itertools.combinations(range(11,23),3 if k==case['shared'] else 2):
   for w in block:edge(v,w)
   if clean() and host(k+1):return True
   for w in block:remove(v,w)
  return False
 try:ok=host(0);status='FOUND' if ok else 'EXHAUSTED'
 except TimeoutError:status='UNKNOWN'
 results.append({'omitted':case['omitted'],'shared':case['shared'],'internal':case['internal'],'af':case['af'],'bf':case['bf'],'status':status,'nodes':nodes,'complete_star_assignments':leaves});print(results[-1],flush=True)
 if time.monotonic()-start>60:break
(p/'independent-results.json').write_text(json.dumps({'method':'Static F-star order, direct full32vertex C4 tests on every added subset, residual E degrees rederived from support masks; no author code imports or early empty capacity pruning.','seconds':time.monotonic()-start,'results':results},indent=2)+'\n')
