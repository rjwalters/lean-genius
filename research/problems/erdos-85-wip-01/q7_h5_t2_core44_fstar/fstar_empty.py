"""Distinct no-C/F-sharing star incidence projection; no ordinary completion."""
import pathlib,json,itertools,time,math
P=pathlib.Path(__file__).parent;deadline=time.monotonic()+60;results=[]
for case in json.loads((P/'four-pattern-results.json').read_text())['results']:
 nodes=0;choices=[]
 for af,bf in itertools.product([3,4],[1,2]):
  g=list(map(set,case['skeleton']))+[set() for _ in range(5)]
  def edge(u,v):g[u].add(v);g[v].add(u)
  for c in range(5):edge(27+c,c);edge(27+c,10)
  for u,v in [(28,30),(23,27+af),(24,27+bf)]:edge(u,v)
  def clean():return all(len(g[u]&g[v])<=1 for u,v in itertools.combinations(range(32),2))
  if not clean():
   choices.append(dict(af=af,bf=bf,status='INVALID_SKELETON'));continue
  def legal(u,v):return v not in g[u] and all(not g[v]&g[w] for w in g[u])
  targets=[4,3,3,3,3,3,2,2,3,2,2,2]
  def empty_graph():
   rem=[targets[i]-len(g[11+i]&set(range(11,23))) for i in range(12)]
   def fill(done):
    global nodes
    nodes+=1
    if nodes>100000 or time.monotonic()>deadline:raise TimeoutError
    if done==4095:return [sorted(ns) for ns in g]
    domains=[]
    for i in range(12):
     if done>>i&1:continue
     opts=[j for j in range(12) if j!=i and not done>>j&1 and rem[j]>0 and legal(11+i,11+j)]
     if len(opts)<rem[i]:return None
     domains.append((math.comb(len(opts),rem[i]),i,opts))
    _,i,opts=min(domains);need=rem[i]
    for group in itertools.combinations(opts,need):
     added=[]
     for j in group:
      if not legal(11+i,11+j):break
      edge(11+i,11+j);rem[j]-=1;added.append(j)
     else:
      rem[i]=0;ans=fill(done|1<<i);rem[i]=need
      if ans:return ans
     for j in added:g[11+i].remove(11+j);g[11+j].remove(11+i);rem[j]+=1
    return None
   return fill(0)
  def dfs(todo):
   global nodes
   nodes+=1
   if nodes>100000 or time.monotonic()>deadline:raise TimeoutError
   if any(len(g[e]&set(range(11,23)))+sum(legal(e,f) for f in range(11,23) if f!=e)<targets[e-11] for e in range(11,23)):return None
   if not todo:
    return empty_graph()
   domains=[]
   for s in todo:
    es=[e for e in range(11,23) if legal(s,e)]
    pairs=[(e,f) for e,f in itertools.combinations(es,2) if not g[e]&g[f]]
    domains.append((len(pairs),s,pairs))
   _,s,pairs=min(domains)
   for es in pairs:
    for e in es:edge(s,e)
    ans=dfs([v for v in todo if v!=s])
    if ans:return ans
    for e in es:g[s].remove(e);g[e].remove(s)
   return None
  try:
   witness=dfs(list(range(27,32)));status='PARTIAL_WITNESS' if witness else 'EXHAUSTED'
  except TimeoutError:witness=None;status='CAPPED'
  choices.append(dict(af=af,bf=bf,status=status,adjacency=witness))
  if status=='CAPPED':break
 results.append(dict(omitted=case['omitted'],nodes=nodes,choices=choices))
 print(case['omitted'],nodes,[r['status'] for r in choices],flush=True)
(P/'fstar-empty-results.json').write_text(json.dumps(dict(results=results,scope='No-sharing F-star incidence projection only. Exact empty degrees included; ordinary singleton edges absent.'),indent=2)+'\n')
