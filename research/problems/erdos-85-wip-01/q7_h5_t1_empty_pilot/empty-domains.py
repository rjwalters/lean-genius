"""Necessary empty-neighbour domains for saved partials, not whole cores."""
import json,itertools,hashlib
from pathlib import Path
p=Path(__file__).parent;rows=[]
for name in ['singleton-results.json','singleton-tail-results.json']:
 raw=(p/name).read_bytes()
 for row in json.loads(raw)['rows']:
  if row['status']!='PASS':continue
  g=[set() for _ in range(49)]
  for a,b in row['partial_graph_edges']:g[a].add(b);g[b].add(a)
  support={v:g[v]&set(range(5)) for v in range(5,36)};demand={v:7-len(g[v]) for v in support};domains=[]
  def extend(left,chosen):
   if not left:domains.append(chosen);return
   c=min(left)
   for v in support:
    if demand[v] and c in support[v] and support[v]<=left and all(not(g[v]&g[w]) for w in chosen):extend(left-support[v],chosen+[v])
  extend(set(range(5)),[])
  assert len(domains)==len({tuple(sorted(d)) for d in domains})
  availability={v:sum(v in d for d in domains) for v in support if demand[v]}
  # Same domain cannot repeat: each contains at least two guests, making C4.
  shortage={v:[demand[v],n] for v,n in availability.items() if n<demand[v]}
  rows.append({'core_index':row['core_index'],'input':name,'input_sha256':hashlib.sha256(raw).hexdigest(),'demand':demand,'domains':domains,'domain_count':len(domains),'vertex_domain_shortages':shortage,'scope':'Single saved singleton completion only; no core exclusion.'})
out={'rows':rows,'scope':'All possible nonempty-support neighbours of one empty vertex in each fixed saved graph. Edges between empty vertices remain absent.'}
(p/'empty-domains.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps([{k:r[k] for k in ['core_index','domain_count','vertex_domain_shortages']} for r in rows]))
