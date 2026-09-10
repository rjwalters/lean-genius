"""Independent set-based completion of the two fixed survivors."""
import pathlib,json,itertools,time
P=pathlib.Path(__file__).parent;deadline=time.monotonic()+60;results=[]
for branch in json.loads((P/'propagation-results.json').read_text())['results']:
 for case in branch['cases']:
  if case['status']!='UNRESOLVED':continue
  count=0
  def solve(adj):
   global count
   count+=1
   if count>100000 or time.monotonic()>deadline:raise TimeoutError
   g=[set(ns) for ns in adj]
   while True:
    forced=None;requirements=[];degrees=[]
    for u in range(48,4,-1):
     missing=[c for c in range(5) if not g[u]&g[c]];need=7-len(g[u])
     if need<0 or (need==0 and missing):return False
     if not need:continue
     candidates=[v for v in range(48,4,-1) if v!=u and v not in g[u] and len(g[v])<7 and all(not g[v]&g[w] for w in g[u])]
     if len(candidates)<need:return False
     degrees.append((len(candidates),u,need,candidates))
     if len(candidates)==need:forced=(u,candidates[0]);break
     for c in reversed(missing):
      targets=[v for v in candidates if c in g[v]]
      if not targets:return False
      requirements.append((len(targets),u,c,targets))
      if len(targets)==1:forced=(u,targets[0]);break
     if forced:break
    if not forced:break
    u,v=forced;g[u].add(v);g[v].add(u)
   if not degrees:return True
   if requirements:
    _,u,c,targets=min(requirements,key=lambda r:(r[0],-r[1],-r[2]));options=[(v,) for v in targets]
   else:
    _,u,need,targets=min(degrees,key=lambda r:(r[0],-r[1]));options=itertools.combinations(targets,need)
   for group in options:
    trial=[set(ns) for ns in g]
    for v in group:trial[u].add(v);trial[v].add(u)
    if any(len(trial[a]&trial[b])>1 for a,b in itertools.combinations(range(49),2)):continue
    if solve(trial):return True
   return False
  try:
   exists=solve(case['adjacency']);status='COMPLETION' if exists else 'EXHAUSTED'
  except TimeoutError:status='CAPPED'
  result=dict(heavy_index=case['heavy_index'],status=status,nodes=count);results.append(result);print(result)
(P/'independent-completion-results.json').write_text(json.dumps(results,indent=2)+'\n')
