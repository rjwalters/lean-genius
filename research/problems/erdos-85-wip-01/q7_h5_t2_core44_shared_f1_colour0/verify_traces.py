"""Independent set-based validation of recorded forced-edge certificates."""
import pathlib,json
P=pathlib.Path(__file__).parent
empties=json.loads((P/'empty-slot-results.json').read_text())['results'];heavies=json.loads((P/'heavy-slot-results.json').read_text())['results'];traces=json.loads((P/'propagation-results.json').read_text())['results'];checked=0;edges=0;negative=0
for bi,branch in enumerate(traces):
 assert branch['unvisited']==0
 for case in branch['cases']:
  h=heavies[bi]['survivors'][case['heavy_index']];g=list(map(set,empties[bi]['survivors'][h['empty_index']]['adjacency']))
  for u,v in h['edges']:g[u].add(v);g[v].add(u)
  def opts(u):return [v for v in range(5,49) if u!=v and v not in g[u] and len(g[v])<7 and len(g[u])<7 and all(not g[v]&g[w] for w in g[u])]
  def missing(u):return [c for c in range(5) if not g[u]&g[c]]
  for u,v in case['added']:
   choices=opts(u);assert v in choices
   forced=len(choices)==7-len(g[u]) or any([w for w in choices if c in g[w]]==[v] for c in missing(u))
   assert forced,(bi,case['heavy_index'],u,v)
   g[u].add(v);g[v].add(u);edges+=1
  if case['status']=='REJECTED':
   reason,u,*rest=case['reason']
   if reason=='degree_capacity':assert len(opts(u))<7-len(g[u])
   elif reason=='colour_capacity':assert rest[0] in missing(u) and not any(rest[0] in g[v] for v in opts(u))
   elif reason=='degree_colour':assert len(g[u])>7 or (len(g[u])==7 and missing(u))
   else:raise AssertionError(reason)
   negative+=1
  else:
   assert case['status']=='UNRESOLVED' and [sorted(ns) for ns in g]==case['adjacency']
  checked+=1
out=dict(status='PASS',traces=checked,forced_edges=edges,confirmed_terminal_negatives=negative,method='Direct graph-set C4/degree candidates and common-high-neighbour tests; no author bitmask propagation imports',scope='Recorded propagation traces only; preceding domain cover and two terminal searches separate')
print(out);(P/'trace-verification.json').write_text(json.dumps(out,indent=2)+'\n')
