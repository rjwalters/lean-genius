"""T2 singleton/empty-incidence necessary search, three previously positive cores."""
import sys,itertools,json,time,hashlib
from pathlib import Path
BASE=Path('/Users/rwalters/GitHub/lean-genius/.codex/worktrees/erdos85-sol2-integration/research/problems/erdos-85-wip-01/q7_h5_heavy_core')
sys.path.insert(0,str(BASE));from host_pilot import hostings
source=json.loads((BASE/'core-t2.json').read_text());masks=source['masks'];n=len(masks)
caps=[4+sum(bool(m>>c&1) for m in masks if m.bit_count()==3) for c in range(5)]
supports=masks+[1<<c for c in range(5) for _ in range(caps[c])];vertices=list(range(5,5+len(supports)));S=list(range(5+n,5+len(supports)));colour={v:supports[v-5].bit_length()-1 for v in S}
start=time.monotonic();deadline=start+60;results=[]
def members(bits):
 while bits:
  low=bits&-bits;yield low.bit_length()-1;bits-=low
for core in [1,2120,9217]:
 if time.monotonic()>deadline:break
 nodes=0;hosts_tried=0;terminals=0;capacity_cuts=0;found=None;capped=False;maxrows=0
 def tick():
  global nodes
  nodes+=1
  if nodes>100000 or time.monotonic()>deadline:raise TimeoutError
 H=[set() for _ in masks]
 for i,(u,v) in enumerate(itertools.combinations(range(n),2)):
  if core>>i&1:H[u].add(v);H[v].add(u)
 options=[hostings([u for u in range(n) if not any(masks[v]>>c&1 for v in H[u])],masks,H,caps[c]) for c in range(5)]
 try:
  for groups in itertools.product(*options):
   paired=[g for block in groups for g in block if len(g)==2]
   if len(paired)!=len(set(paired)):continue
   hosts_tried+=1;G=[0]*49
   def edge(u,v):G[u]|=1<<v;G[v]|=1<<u
   for v,mask in enumerate(supports,5):
    for c in range(5):
     if mask>>c&1:edge(v,c)
   for u in range(n):
    for v in H[u]:edge(u+5,v+5)
   offset=5+n
   for c,bins in enumerate(groups):
    for j,group in enumerate(bins):
     for u in group:edge(offset+j,u+5)
    offset+=caps[c]
   needs=[0]*49
   for v in S:
    for c in range(5):
     if not G[v]&G[c]:needs[v]|=1<<c
   demand=[0]*49
   for v in vertices:demand[v]=7-G[v].bit_count()-(needs[v].bit_count() if v in colour else 0)
   assert min(demand)>=0 and sum(demand[v]*supports[v-5].bit_count() for v in vertices)==60
   rows=[]
   def build(uncovered,chosen):
    tick()
    if not uncovered:rows.append(tuple(chosen));return
    c=(uncovered&-uncovered).bit_length()-1
    for v in vertices:
     mask=supports[v-5]
     if demand[v] and mask>>c&1 and mask&uncovered==mask and all(not G[v]&G[w] for w in chosen):build(uncovered^mask,chosen+[v])
   build(31,[]);maxrows=max(maxrows,len(rows));vrows=[0]*49;pairrows={}
   for i,row in enumerate(rows):
    for v in row:vrows[v]|=1<<i
    for pair in itertools.combinations(sorted(row),2):pairrows[pair]=pairrows.get(pair,0)|(1<<i)
   def capacity(active,remaining,slots):
    return active.bit_count()>=slots and all((active&vrows[v]).bit_count()>=remaining[v] for v in vertices if remaining[v])
   def cover(active,remaining,slots,chosen):
    tick()
    if not any(remaining):return chosen if slots==0 else None
    if slots==0 or not capacity(active,remaining,slots):return None
    v=min((v for v in vertices if remaining[v]),key=lambda v:(active&vrows[v]).bit_count())
    for i in members(active&vrows[v]):
     row=rows[i]
     if any(remaining[u]==0 for u in row):continue
     rest=list(remaining)
     for u in row:rest[u]-=1
     bad=1<<i
     for pair in itertools.combinations(sorted(row),2):bad|=pairrows[pair]
     allowed=active&~bad
     for u in row:
      if rest[u]==0:allowed&=~vrows[u]
     answer=cover(allowed,rest,slots-1,chosen+[i])
     if answer is not None:return answer
    return None
   def allowed(u,v):return u!=v and not(G[u]>>v&1) and all(not G[b]&G[w] for a,b in [(u,v),(v,u)] for w in members(G[a]))
   def search(active):
    global terminals,capacity_cuts
    tick()
    if not capacity(active,demand,12):capacity_cuts+=1;return None
    best=None
    for u in S:
     for c in members(needs[u]):
      cand=[v for v in S if colour[v]==c and needs[v]>>colour[u]&1 and allowed(u,v)]
      if not cand:return None
      if best is None or len(cand)<len(best[2]):best=(u,c,cand)
    if best is None:
     terminals+=1;answer=cover(active,demand,12,[])
     return dict(adjacency=list(G),empty_rows=[rows[i] for i in answer],hosts=groups) if answer is not None else None
    u,c,cand=best
    for v in cand:
     bad=0
     for a,b in [(u,v),(v,u)]:
      for w in members(G[a]):bad|=pairrows.get(tuple(sorted((b,w))),0)
     edge(u,v);needs[u]^=1<<c;needs[v]^=1<<colour[u]
     answer=search(active&~bad)
     if answer is not None:return answer
     G[u]^=1<<v;G[v]^=1<<u;needs[u]^=1<<c;needs[v]^=1<<colour[u]
    return None
   found=search((1<<len(rows))-1)
   if found is not None:break
 except TimeoutError:capped=True
 result=dict(core=core,status='PARTIAL_INCIDENCE' if found else 'CAPPED' if capped else 'EXCLUDED_EMPTY_INCIDENCE',nodes=nodes,hosts_tried=hosts_tried,singleton_terminals=terminals,capacity_cuts=capacity_cuts,max_initial_empty_rows=maxrows,witness=found)
 results.append(result);print({k:v for k,v in result.items() if k!='witness'},flush=True)
Path('results.json').write_text(json.dumps(dict(results=results,seconds=time.monotonic()-start,unvisited=3-len(results),caps=dict(nodes_per_core=100000,wall_seconds=60),scope='Three previously singleton-positive T2 cores only; all host sizes, monotone empty-row capacity, terminal exact incidence cover. Empty-empty edges absent; five earlier capped cores untouched.'),indent=2)+'\n')
