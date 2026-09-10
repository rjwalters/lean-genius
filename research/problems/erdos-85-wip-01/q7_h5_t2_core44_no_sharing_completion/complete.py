from pathlib import Path
import json,itertools,time,math,hashlib
p=Path(__file__).parent;src=p/'results.json';d=json.loads(src.read_text());start=time.monotonic();results=[]
def vertices(bits):
 while bits:
  b=bits&-bits;yield b.bit_length()-1;bits^=b
for case in d['results']:
 nodes=0
 def tick():
  global nodes
  nodes+=1
  if nodes>100000 or time.monotonic()-start>60:raise TimeoutError
 def legal(g,u,v):return not(g[u]>>v&1) and not any(g[w]&g[v] for w in vertices(g[u]))
 def solve(g):
  tick()
  while True:
   deg=[x.bit_count() for x in g]
   if any(deg[u]>7 for u in range(5,49)):return None
   cand=[[] for _ in range(49)]
   for u,v in itertools.combinations(range(5,49),2):
    if deg[u]<7 and deg[v]<7 and legal(g,u,v):cand[u].append(v);cand[v].append(u)
   forced=None;choices=[]
   for u in range(5,49):
    need=7-deg[u]
    if len(cand[u])<need:return None
    if need:
     choices.append((math.comb(len(cand[u]),need),'degree',u,need,cand[u]))
     if len(cand[u])==need:forced=(u,cand[u][0]);break
    for c in range(5):
     if g[u]&g[c]:continue
     opts=[v for v in cand[u] if g[v]>>c&1]
     if not opts:return None
     choices.append((len(opts),'colour',u,1,opts))
     if len(opts)==1:forced=(u,opts[0]);break
    if forced:break
   if forced:
    u,v=forced;g[u]|=1<<v;g[v]|=1<<u;continue
   if not choices:
    assert all(x.bit_count()==(8 if u<5 else 7) for u,x in enumerate(g))
    assert all((g[u]&g[v]).bit_count()<=1 for u,v in itertools.combinations(range(49),2))
    assert all((g[u]&g[c]).bit_count()==1 for u in range(5,49) for c in range(5))
    return g
   _,kind,u,need,opts=min(choices)
   for group in itertools.combinations(opts,need):
    h=g.copy();good=True
    for v in group:
     if not legal(h,u,v):good=False;break
     h[u]|=1<<v;h[v]|=1<<u
    if good:
     ans=solve(h)
     if ans is not None:return ans
   return None
 try:witness=solve(case['adjacency'].copy());status='FULL_GRAPH' if witness is not None else 'EXHAUSTED'
 except TimeoutError:witness=None;status='UNKNOWN'
 r={k:case[k] for k in ['af','bf','omitted','f3_d3_edge']};r.update(status=status,nodes=nodes,adjacency=witness);results.append(r);print({k:v for k,v in r.items() if k!='adjacency'},flush=True)
 if time.monotonic()-start>60:break
(p/'completion-results.json').write_text(json.dumps(dict(source_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),results=results,unvisited=len(d['results'])-len(results),seconds=time.monotonic()-start,node_cap_per_case=100000,wall_cap_seconds=60,scope='Full graph completion on new own-colour normalized49vertex domain; no retry of earlier capped trees.'),indent=2)+'\n')
