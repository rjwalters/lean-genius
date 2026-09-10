"""Bounded completion of the two survivors of the new colour0 domain."""
import pathlib,json,itertools,time
from propagate import propagate
P=pathlib.Path(__file__).parent;deadline=time.monotonic()+60;results=[]
for branch in json.loads((P/'propagation-results.json').read_text())['results']:
 for case in branch['cases']:
  if case['status']!='UNRESOLVED':continue
  nodes=0
  def dfs(adj):
   global nodes
   nodes+=1
   if nodes>100000 or time.monotonic()>deadline:raise TimeoutError
   fixed=propagate(adj,deadline)
   if fixed['status']=='WALL_LIMIT':raise TimeoutError
   if fixed['status']=='REJECTED':return None
   if fixed['status']=='COMPLETE':return fixed['adjacency']
   g=list(map(set,fixed['adjacency']));mask=[sum(1<<c for c in ns if c<5) for ns in g];missing=[]
   for u in range(49):
    covered=0
    for v in g[u]:
     if v>=5:covered|=mask[v]
    missing.append(31^covered)
   def legal(u,v):return u!=v and v not in g[u] and len(g[u])<7 and len(g[v])<7 and mask[v]&missing[u]==mask[v] and mask[u]&missing[v]==mask[u] and all(not g[v]&g[w] for w in g[u])
   colour_choices=[];degree_choices=[]
   for u in range(5,49):
    if len(g[u])==7:continue
    opts=[v for v in range(5,49) if legal(u,v)]
    degree_choices.append((len(opts),u,opts))
    for c in range(5):
     if missing[u]>>c&1:
      choices=[v for v in opts if mask[v]>>c&1];colour_choices.append((len(choices),u,c,choices))
   if colour_choices:
    _,u,c,choices=min(colour_choices);groups=[(v,) for v in choices]
   else:
    _,u,opts=min(degree_choices);groups=itertools.combinations(opts,7-len(g[u]))
   for group in groups:
    trial=[set(ns) for ns in g]
    for v in group:trial[u].add(v);trial[v].add(u)
    if any(len(trial[a]&trial[b])>1 for a,b in itertools.combinations(range(49),2)):continue
    answer=dfs(trial)
    if answer:return answer
   return None
  try:
   witness=dfs(case['adjacency']);status='COMPLETE' if witness else 'EXHAUSTED'
  except TimeoutError:witness=None;status='CAPPED'
  row=dict(omitted=branch['omitted'],internal=branch['internal'],heavy_index=case['heavy_index'],nodes=nodes,status=status,adjacency=witness);results.append(row);print({k:v for k,v in row.items() if k!='adjacency'},flush=True)
(P/'completion-results.json').write_text(json.dumps(dict(results=results,scope='Two remaining graphs of new colour0-labelled decomposition; full-cover and algorithm review required before branch exclusion.'),indent=2)+'\n')
