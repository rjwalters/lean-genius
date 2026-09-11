from pathlib import Path
import itertools,json
p=Path(__file__).resolve().parent;total=valid=0;maximum=-1;witness=None
for loops in itertools.product(range(2),repeat=3):
 for types in itertools.product(range(3),repeat=3):
  adj=[set() for _ in range(6)]
  def edge(a,b):adj[a].add(b);adj[b].add(a)
  for i,v in enumerate(loops):
   if v:edge(2*i,2*i+1)
  for (i,j),v in zip(itertools.combinations(range(3),2),types):
   if v:
    for b in range(2):edge(2*i+b,2*j+(b^(v-1)))
  total+=1
  if any(len(adj[i]&adj[j])>1 for i in range(6) for j in range(i)):continue
  valid+=1;m=sum(map(len,adj))//2
  if m>maximum:maximum=m;witness=[sorted(a) for a in adj]
assert total==216 and maximum==7
result={'status':'COMPLETE','graphs':total,'C4_free_graphs':valid,'maximum_edges':maximum,'sharpness_adjacency':witness,'scope':'Local six-vertex necessary-domain check only.'}
(p/'verification.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
