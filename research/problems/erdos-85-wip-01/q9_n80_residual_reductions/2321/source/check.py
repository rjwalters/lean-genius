from pathlib import Path
import itertools as it,json,time
start=time.monotonic();p=Path(__file__).resolve().parent;records=[];tested=degreepass=0;classes={}
pairs=list(it.combinations(range(4),2));perms=[a+b for a in it.permutations((0,1)) for b in it.permutations((2,3))]
transports=[tuple(2*perm[i]+(b^flip[i]) for i in range(4) for b in range(2)) for perm in perms for flip in it.product(range(2),repeat=4)]
for loops in it.product(range(2),repeat=4):
 for cross in it.product(range(3),repeat=6):
  if time.monotonic()-start>30:raise TimeoutError('Original30s cap exceeded')
  tested+=1;degrees=list(loops)
  for (i,j),v in zip(pairs,cross):
   if v:degrees[i]+=1;degrees[j]+=1
  if degrees!=[2,2,3,3]:continue
  degreepass+=1;adj=[set() for _ in range(8)]
  def edge(a,b):adj[a].add(b);adj[b].add(a)
  for i,v in enumerate(loops):
   if v:edge(2*i,2*i+1)
  for (i,j),v in zip(pairs,cross):
   if v:
    for b in range(2):edge(2*i+b,2*j+(b^(v-1)))
  if any(len(adj[i]&adj[j])>1 for i in range(8) for j in range(i)):continue
  edges=[(i,j) for i in range(8) for j in adj[i] if i<j]
  enc=lambda t:tuple(sorted(tuple(sorted((t[i],t[j]))) for i,j in edges))
  canonical=min(map(enc,transports));record={'loops':loops,'cross':cross,'edges':sorted(edges)}
  records.append(record);classes.setdefault(canonical,[]).append(record)
result={'status':'COMPLETE','original_cap_seconds':30,'seconds':time.monotonic()-start,'tested':tested,'degree_pass':degreepass,'C4_free':len(records),'equivariant_classes':len(classes),'classes':[{'representative_edges':edges,'count':len(rs),'loop_degree_types':sorted(set(tuple(sorted(degrees for degrees,l in zip([2,2,3,3],r['loops']) if l)) for r in rs))} for edges,rs in sorted(classes.items())],'records':records}
assert tested==11664 and len(classes)==3
(p/'results.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k!='records'}))
