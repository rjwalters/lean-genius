"""Bounded joint completion of fixed H7 positive incidence assignments."""
from pathlib import Path
import json,itertools,time,hashlib
p=Path(__file__).parent;local=json.loads((p/'results.json').read_text());raw=Path('/Users/rwalters/GitHub/lean-genius/.codex/worktrees/erdos85-sol2-integration/research/problems/erdos-85-wip-01/q7_h7_labelled_incidence/pilot-1.json').read_bytes();assert hashlib.sha256(raw).hexdigest()==local['input_sha256'];selected={r['empty_mask'] for r in local['rows'] if not r['failures']};start=time.monotonic();out=[]
for row in json.loads(raw)['results']:
 if row['mask'] not in selected:continue
 g=[set() for _ in range(49)]
 for a,b in row['witness']['partial_edges']:g[a].add(b);g[b].add(a)
 vertices=list(range(14,49));support={v:g[v]&set(range(7)) for v in vertices};missing={v:set(range(7)) for v in vertices};nodes=0;limited=False
 def search():
  global nodes,limited
  nodes+=1
  if nodes>100000 or time.monotonic()-start>60:limited=True;return False
  best=None
  for v in vertices:
   n=7-len(g[v]);m=len(missing[v])
   if n<0 or m<n or m>2*n:return False
   for c in sorted(missing[v]):
    choices=[w for w in vertices if w!=v and w not in g[v] and len(g[w])<7 and c in support[w] and support[w]<=missing[v] and support[v]<=missing[w] and not any(g[w]&g[x] for x in g[v])]
    if not choices:return False
    if best is None or len(choices)<len(best[1]):best=(v,choices)
  if best is None:return True
  v,choices=best
  for w in choices:
   g[v].add(w);g[w].add(v);missing[v]-=support[w];missing[w]-=support[v]
   if search():return True
   g[v].remove(w);g[w].remove(v);missing[v]|=support[w];missing[w]|=support[v]
   if limited:return False
  return False
 ok=search();edges=None
 if ok:
  assert all(len(g[v])==(8 if v<7 else 7) for v in range(49))
  assert all(len(g[a]&g[b])<=1 for a,b in itertools.combinations(range(49),2))
  edges=[[a,b] for a in range(49) for b in sorted(g[a]) if a<b]
 out.append({'empty_mask':row['mask'],'status':'FULL_GRAPH' if ok else 'UNKNOWN' if limited else 'REJECT_FIXED_INCIDENCE','nodes':nodes,'full_edges':edges})
 if time.monotonic()-start>60:break
result={'input_sha256':hashlib.sha256(raw).hexdigest(),'selected':len(selected),'processed':len(out),'seconds':time.monotonic()-start,'caps':{'nodes_per_fixed_graph':100000,'seconds_total':60},'scope':'Fixed saved incidence assignments only; no whole-class exclusion and no retry of capped original incidence trees.','counts':{s:sum(r['status']==s for r in out) for s in ['FULL_GRAPH','REJECT_FIXED_INCIDENCE','UNKNOWN']},'rows':out};(p/'joint-results.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k!='rows'}))
