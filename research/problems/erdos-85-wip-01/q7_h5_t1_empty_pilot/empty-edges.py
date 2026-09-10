"""Finish empty-empty edges for three fixed domain-cover witnesses."""
import json,itertools,time
from pathlib import Path
p=Path(__file__).parent;domains={r['core_index']:r for r in json.loads((p/'empty-domains.json').read_text())['rows']};partials={r['core_index']:r for name in ['singleton-results.json','singleton-tail-results.json'] for r in json.loads((p/name).read_text())['rows'] if r['status']=='PASS'};out=[];start=time.monotonic()
for row in json.loads((p/'empty-cover-results.json').read_text())['rows']:
 if row['status']!='PASS':continue
 g=[set() for _ in range(49)]
 def edge(a,b):g[a].add(b);g[b].add(a)
 for a,b in partials[row['core_index']]['partial_graph_edges']:edge(a,b)
 for k,d in enumerate(row['selected_domains']):
  for v in domains[row['core_index']]['domains'][d]:edge(36+k,v)
 assert all(len(g[v])==7 for v in range(5,36))
 assert all(len(g[a]&g[b])<=1 for a,b in itertools.combinations(range(49),2))
 base=[[a,b] for a in range(49) for b in sorted(g[a]) if a<b];nodes=0;limited=False
 def dfs():
  global nodes,limited
  nodes+=1
  if nodes>100000 or time.monotonic()-start>60:limited=True;return False
  options=[]
  for v in range(36,49):
   n=7-len(g[v])
   if n:
    choices=[w for w in range(36,49) if w!=v and len(g[w])<7 and w not in g[v] and not any(g[w]&g[x] for x in g[v])]
    if len(choices)<n:return False
    options.append((len(choices),v,n,choices))
  if not options:return True
  _,v,n,choices=min(options)
  for block in itertools.combinations(choices,n):
   added=[];ok=True
   for w in block:
    if any(g[w]&g[x] for x in g[v]):ok=False;break
    edge(v,w);added.append(w)
   if ok and dfs():return True
   for w in added:g[v].remove(w);g[w].remove(v)
   if limited:return False
  return False
 ok=dfs()
 if ok:
  assert all(len(g[v])==(8 if v<5 else 7) for v in range(49))
  assert all(len(g[a]&g[b])<=1 for a,b in itertools.combinations(range(49),2))
 out.append({'core_index':row['core_index'],'status':'FULL_GRAPH' if ok else 'UNKNOWN' if limited else 'REJECT_FIXED_EMPTY_COVER','nodes':nodes,'base_edges':base,'full_edges':[[a,b] for a in range(49) for b in sorted(g[a]) if a<b] if ok else None})
result={'scope':'Only first saved singleton completion and first empty-neighbour cover for each tested core. Failure is not core exclusion.','rows':out};(p/'empty-edges-results.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps([{k:r[k] for k in ['core_index','status','nodes']} for r in out]))
