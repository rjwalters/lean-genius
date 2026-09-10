"""Empty-induced graph necessity before singleton assignments; bounded new domain."""
import pathlib,json,itertools,time,math
BASE=pathlib.Path(__file__).parent
patterns=json.loads((BASE/'core210-pattern.json').read_text());masks=[7,25,10,18,12,20];start=time.monotonic();deadline=start+60;results=[]
from host_constraint_bins import feasible
failed_patterns={(210,0)}
for case in patterns:
 for index,pattern in enumerate(case['patterns']):
  if (case["core"],index) not in failed_patterns:continue
  if time.monotonic()>deadline:break
  G=[set() for _ in range(23)];E=list(range(11,23));rem=list(pattern['empty_degrees']);nodes=0
  def edge(u,v):G[u].add(v);G[v].add(u)
  for u,m in enumerate(masks,5):
   for c in range(5):
    if m>>c&1:edge(u,c)
  for i,(u,v) in enumerate(itertools.combinations(range(6),2)):
   if case['core']>>i&1:edge(5+u,5+v)
  for e,guests in enumerate(pattern['heavy_rows'],11):
   for h in guests:edge(e,5+h)
  assert all(len(G[u]&G[v])<=1 for u,v in itertools.combinations(range(23),2))
  def legal(u,v):return v not in G[u] and all(not G[v]&G[w] for w in G[u])
  def search(done):
   global nodes
   nodes+=1
   if nodes>100000 or time.monotonic()>deadline:raise TimeoutError
   if done.bit_count()%3==0 and not feasible(G,deadline):return None
   if done==4095:return [sorted(s) for s in G]
   best=None
   for i,u in enumerate(E):
    if done>>i&1:continue
    choices=[j for j,v in enumerate(E) if j!=i and not done>>j&1 and rem[j]>0 and legal(u,v)]
    if len(choices)<rem[i]:return None
    score=math.comb(len(choices),rem[i])
    if best is None or score<best[0]:best=(score,i,choices)
   _,i,choices=best;u=E[i];need=rem[i]
   for group in itertools.combinations(choices,need):
    added=[]
    for j in group:
     v=E[j]
     if not legal(u,v):break
     edge(u,v);rem[j]-=1;added.append(j)
    else:
     rem[i]=0;answer=search(done|1<<i);rem[i]=need
     if answer is not None:return answer
    for j in added:G[u].remove(E[j]);G[E[j]].remove(u);rem[j]+=1
   return None
  try:witness=search(0);status='PARTIAL_WITNESS' if witness else 'EXHAUSTED'
  except TimeoutError:witness=None;status='CAPPED'
  row=dict(core=case['core'],pattern=index,status=status,nodes=nodes,adjacency=witness);results.append(row);print({k:v for k,v in row.items() if k!='adjacency'},flush=True)
pathlib.Path('verification-results.json').write_text(json.dumps(dict(results=results,seconds=time.monotonic()-start,visited=len(results),total_patterns=len(failed_patterns),caps=dict(nodes_per_pattern=100000,wall_seconds=60),scope='Core210: all empty-induced graph completions under necessary local singleton-host partitions. No twin normalization; no singleton cap retried.'),indent=2)+'\n')
