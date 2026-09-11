from pathlib import Path
from itertools import permutations,product
import time,json
start=time.monotonic();WALL=60;NODE=100000
out=[]
def pair(a,b):return min((a,b),(a^1,b^1))
roots=[]
for pp in permutations(range(3)):
 for bits in product(range(2),repeat=3):
  if sum(bits)%2!=1:continue
  roots.append(tuple(2*pp[x//2]+((x%2)^bits[x//2]) for x in range(6)))
for pi in sorted(roots):
 keys=[]
 for kind in range(3):
  keys.extend((kind,*q) for q in sorted({pair(a,b) for a in range(6) for b in range(6) if b!=(pi[a] if kind==2 else a)}))
 ix={key:i for i,key in enumerate(keys)};assert len(ix)==45
 triples=[];masks=[];bycol=[[] for _ in keys]
 for x,y,z in product(range(0,6,2),range(6),range(6)):
  if x==y or x==z or z==pi[y]:continue
  cols=[ix[(0,*pair(x,y))],ix[(1,*pair(x,z))],ix[(2,*pair(y,z))]]
  mask=sum(1<<c for c in cols);assert mask.bit_count()==3
  idx=len(triples);triples.append((x,y,z));masks.append(mask)
  for c in cols:bycol[c].append(idx)
 nodes=0;aborted=False
 def dfs(used,chosen):
  global nodes,aborted
  nodes+=1
  if nodes>NODE or time.monotonic()-start>WALL:aborted=True;return None
  if used==(1<<45)-1:return chosen
  best=None
  for c in range(45):
   if used>>c&1:continue
   choices=[j for j in bycol[c] if not masks[j]&used]
   if not choices:return None
   if best is None or len(choices)<len(best):best=choices
  for j in best:
   found=dfs(used|masks[j],chosen+[j])
   if found is not None:return found
   if aborted:return None
  return None
 chosen=dfs(0,[])
 status='WITNESS' if chosen is not None else ('UNKNOWN' if aborted else 'EXCLUDED')
 witness=[] if chosen is None else [list(triples[j]) for j in chosen]
 if chosen is not None:
  expanded=[t for x,y,z in witness for t in [(x,y,z),(x^1,y^1,z^1)]];assert len(set(expanded))==30
  for a,b in [(0,1),(0,2),(1,2)]:assert len({(t[a],t[b]) for t in expanded})==30
 out.append({'pi':pi,'status':status,'nodes':nodes,'candidate_orbits':len(triples),'witness_orbits':witness})
result={'scope':'Local residual label triples only; no residual edges or full graph','original_wall_seconds':WALL,'original_node_cap_per_root':NODE,'seconds':time.monotonic()-start,'roots':out,'counts':{s:sum(r['status']==s for r in out) for s in ['WITNESS','EXCLUDED','UNKNOWN']}}
Path(__file__).with_name('results.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k!='roots'},indent=2));print('nodes',sum(r['nodes'] for r in out), 'max',max(r['nodes'] for r in out))
