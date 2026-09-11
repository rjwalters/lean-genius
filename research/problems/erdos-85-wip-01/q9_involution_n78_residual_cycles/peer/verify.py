from pathlib import Path
from itertools import combinations,permutations
from collections import Counter
import json,hashlib
p=Path('/Users/rwalters/lean-genius-q9-known-values-20260911/involution-n78-residual-cycles');out=Path(__file__).parent
pins=json.loads((p/'pins.json').read_text())
for n,h in pins.items():assert hashlib.sha256((p/n).read_bytes()).hexdigest()==h,n
stats={}
for length in (3,5):
 hist=Counter();count=0
 for vertices in combinations(range(8),length):
  for tail in permutations(vertices[1:]):
   if tail[0]>tail[-1]:continue
   seq=(vertices[0],)+tail
   edges={tuple(sorted((seq[i],seq[(i+1)%length]))) for i in range(length)}
   other={tuple(sorted((a^1,b^1))) for a,b in edges}
   assert edges!=other
   union=edges|other;hist[len(union)]+=1;count+=1
   if length==5:assert len(union)>=7
   else:
    overlap=set(vertices)&{v^1 for v in vertices};assert len(overlap) in (0,2)
    if overlap:
     adj=[set() for _ in range(8)]
     for a,b in union:adj[a].add(b);adj[b].add(a)
     assert any(len(adj[a]&adj[b])>=2 for a,b in combinations(range(8),2))
 stats[length]={'cycles':count,'union_edge_histogram':dict(hist)}
result={'status':'PASS','source_pins_verified':len(pins),'cycle_checks':stats,'scope':'Independent finite check of cycle/image overlap supporting paper proof; no graph extension or exclusion.'}
(out/'verification.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
(out/'input-pins.json').write_text(json.dumps({str(p/'pins.json'):hashlib.sha256((p/'pins.json').read_bytes()).hexdigest()},indent=2)+'\n')
