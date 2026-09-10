"""Finite edge skeletons implied by colour0 saturation in the C/F-sharing branches."""
import pathlib,json,itertools
P=pathlib.Path(__file__).parent
source=P/'four-pattern-results.json'
results=[];audit=[]
for shared in [1,2]:
 missing=[{0,1,3} for _ in range(5)];missing[shared]={0}
 internal=[]
 for bits in range(1024):
  edges=[(u,v) for i,(u,v) in enumerate(itertools.combinations(range(5),2)) if bits>>i&1]
  degrees=[sum(c in e for e in edges) for c in range(5)]
  if max(degrees)>1:continue
  if any(v not in missing[u] or u not in missing[v] for u,v in edges):continue
  internal.append(edges)
 for case in json.loads(source.read_text())['results']:
  for edges in internal:
   f0_internal=any(0 in e for e in edges)
   for af,bf in itertools.product([None,3,4],[None,1,2]):
    if (af is None or bf is None) and not f0_internal:continue
    if af is None and bf is None:continue
    if bf==shared:continue
    g=list(map(set,case['skeleton']))+[set() for _ in range(5)]
    def edge(u,v):g[u].add(v);g[v].add(u)
    for c in range(5):edge(27+c,c);edge(27+c,10)
    edge(27+shared,7)
    for u,v in edges:edge(27+u,27+v)
    if af is not None:edge(23,27+af)
    if bf is not None:edge(24,27+bf)
    bad=[(u,v) for u,v in itertools.combinations(range(32),2) if len(g[u]&g[v])>1]
    row=dict(shared=shared,omitted=case['omitted'],internal=edges,af=af,bf=bf)
    audit.append(dict(**row,c4_free=not bad))
    if not bad:results.append(dict(**row,adjacency=[sorted(ns) for ns in g]))
out=dict(results=results,audit=audit,scope='Necessary sharing-branch forced-edge skeletons only. Absence of af/bf means the corresponding special is not an F-star target; remaining singleton edges absent.')
(P/'branches.json').write_text(json.dumps(out,indent=2)+'\n')
print({'total':len(results),'counts':{str((s,o)):sum(r['shared']==s and r['omitted']==o for r in results) for s in [1,2] for o in [0,4,7,11]}})
