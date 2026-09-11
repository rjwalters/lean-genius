from pathlib import Path
import json
p=Path(__file__).parent;g=json.loads((p/'group.json').read_text());mul=g['multiplication'];labels=g['center_labels'];checks=0;seen=set()
for c in json.loads((p/'certificates.json').read_text()):
 S=c['S'];assert len(S)==5 and tuple(S) not in seen;seen.add(tuple(S));adj=[set() for _ in range(54)]
 for v in range(48):
  adj[6+v].add(labels[v]);adj[labels[v]].add(6+v)
  for s in S:adj[6+v].add(6+mul[v][s]);adj[6+mul[v][s]].add(6+v)
 cycle=c['cycle'];assert len(cycle)==len(set(cycle))==4
 for u,v in zip(cycle,cycle[1:]+cycle[:1]):assert v in adj[u];checks+=1
assert len(seen)==228 and checks==912
(p/'verification.json').write_text(json.dumps({'cycles':len(seen),'distinct_cycle_vertices':True,'edges_checked':checks,'scope':'Direct certificate edges in F-W plus W graph; fixed matching edges are not needed'},indent=2)+'\n');print(len(seen),'cycles;',checks,'edges verified')
