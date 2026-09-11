from pathlib import Path
import itertools as it,json,time
start=time.monotonic();p=Path(__file__).resolve().parent;pairs=list(it.combinations(range(5),2));target=[1,1,1,2,3];records=[];skeletons=raw=free=0
for loops in it.product(range(2),repeat=5):
 for cross in it.product(range(2),repeat=10):
  if time.monotonic()-start>30:raise TimeoutError('Original30s cap exceeded')
  ds=list(loops)
  for (i,j),b in zip(pairs,cross):
   if b:ds[i]+=1;ds[j]+=1
  if ds!=target:continue
  skeletons+=1;present=[x for x,b in zip(pairs,cross) if b]
  for signs in it.product(range(2),repeat=len(present)):
   raw+=1;adj=[set() for _ in range(10)]
   def edge(a,b):adj[a].add(b);adj[b].add(a)
   for i,b in enumerate(loops):
    if b:edge(2*i,2*i+1)
   for (i,j),s in zip(present,signs):
    for b in range(2):edge(2*i+b,2*j+(b^s))
   if any(len(adj[i]&adj[j])>1 for i in range(10) for j in range(i)):continue
   free+=1;supports=[]
   for vertices in it.combinations(range(10),3):
    if len({v//2 for v in vertices})!=3:continue
    other=tuple(sorted(v^1 for v in vertices))
    if vertices>other:continue
    if sum(len(adj[v]) for v in vertices)>5:continue
    aa=[set(a) for a in adj]+[set(vertices),set(other)]
    for v in vertices:aa[v].add(10)
    for v in other:aa[v].add(11)
    if any(len(aa[i]&aa[j])>1 for i in range(12) for j in range(i)):continue
    endpoints=set().union(*(adj[v] for v in vertices))
    if len(endpoints&set(range(6)))>1:continue
    supports.append(list(vertices))
   records.append({'edges':[(i,j) for i in range(10) for j in sorted(adj[i]) if i<j],'supports':supports})
result={'status':'COMPLETE','original_cap_seconds':30,'seconds':time.monotonic()-start,'degree_skeletons':skeletons,'degree_graphs':raw,'C4_free_graphs':free,'graphs_with_support':sum(bool(r['supports']) for r in records),'support_orbits':sum(len(r['supports']) for r in records),'records':records}
(p/'results.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k!='records'}))
