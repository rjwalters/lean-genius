from pathlib import Path
from itertools import permutations,combinations
import json,hashlib
src=Path('/Users/rwalters/lean-genius-q9-known-values-20260911/involution-six-fixed');out=Path(__file__).parent
pins=json.loads((src/'pins.json').read_text())
for n,h in pins.items():assert hashlib.sha256((src/n).read_bytes()).hexdigest()==h
premise=json.loads((src/'premise.json').read_text());assert hashlib.sha256(Path(premise['source']).read_bytes()).hexdigest()==premise['sha256']
models={'matching':[(0,1),(2,3),(4,5)],'star':[(0,j) for j in range(1,6)],'triangle_leaves':[(0,1),(1,2),(0,2),(0,3),(1,4),(2,5)],'double_star':[(0,1),(0,2),(0,3),(1,4),(1,5)]}
reported=json.loads((src/'explore-results.json').read_text())['survivors_by_order'];result={}
for name,edges in models.items():
 orbit={tuple(sorted(tuple(sorted((g[a],g[b]))) for a,b in edges)) for g in permutations(range(6))}
 adj=[set() for _ in range(6)]
 for a,b in edges:adj[a].add(b);adj[b].add(a)
 degrees=[len(nb) for nb in adj];assert all(d%2 for d in degrees)
 assert all(len(adj[u]&adj[v])<=1 for u,v in combinations(range(6),2))
 profile=','.join(map(str,sorted(degrees)));orders=[]
 for N in (78,80):
  R=N-60+sum(degrees)
  valid=all((9-d)*(2+d)<=R for d in degrees)
  assert (profile in reported[str(N)])==valid
  if valid:
   rec=reported[str(N)][profile];assert rec['count']==len(orbit)
   assert tuple(sorted(tuple(sorted(e)) for e in rec['representative_edges'])) in orbit
   orders.append(N)
 result[name]={'labelled_count':len(orbit),'orders':orders}
assert {k for k in reported['78']}=={','.join(map(str,sorted(len([e for e in edges if i in e]) for i in range(6)))) for name,edges in models.items() if name!='double_star'}
assert len(reported['80'])==4
(out/'verification.json').write_text(json.dumps({'status':'PASS','models':result,'source_pins':len(pins),'scope':'Independent representative/permutation/capacity checks; completeness established by audited paper proof, no full32768 replay.'},indent=2)+'\n')
(out/'input-pins.json').write_text(json.dumps({str(src/'pins.json'):hashlib.sha256((src/'pins.json').read_bytes()).hexdigest(),premise['source']:premise['sha256']},indent=2)+'\n');print(json.dumps(result))
