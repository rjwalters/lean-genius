"""Independent direct saved-edge validation; no search code imported."""
from pathlib import Path
import json,itertools,hashlib
p=Path(__file__).parent;core=json.loads((p/'results.json').read_text());out=[]
for name in ['singleton-results.json','singleton-tail-results.json']:
 if not (p/name).exists():continue
 raw=(p/name).read_bytes();d=json.loads(raw);checked=[]
 for row in d['rows']:
  if row['status']!='PASS':continue
  es=row['partial_graph_edges'];assert len(es)==len(set(map(tuple,es)))
  g=[set() for _ in range(49)]
  for a,b in es:
   assert 0<=a<b<49;g[a].add(b);g[b].add(a)
  expected=[set(s) for s in core['supports']]+[{c} for c,n in enumerate(core['singleton_hosts_by_colour']) for _ in range(n)]+[set() for _ in range(13)]
  assert len(expected)==44
  assert all(g[v]&set(range(5))==expected[v-5] for v in range(5,49))
  assert all(len(g[h])==8 and not(g[h]&set(range(5))) for h in range(5))
  assert [[a-5,b-5] for a,b in es if 5<=a<b<13]==sorted(core['survivors'][row['core_index']]['edges'])
  assert all(len(g[v])<=7 for v in range(5,49))
  assert all(len(g[a]&g[b])<=1 for a,b in itertools.combinations(range(49),2))
  assert all(len(g[v]&g[h])==1 for v in range(5,36) for h in range(5))
  assert all(not g[v] for v in range(36,49))
  checked.append(row['core_index'])
 out.append({'input':name,'sha256':hashlib.sha256(raw).hexdigest(),'checked_positive_core_indices':checked,'status':'PASS'})
(p/'singleton-witness-audit.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
