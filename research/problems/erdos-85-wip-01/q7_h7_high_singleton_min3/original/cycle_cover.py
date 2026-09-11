from pathlib import Path
import itertools,json,collections
p=Path(__file__).parent;g=[set() for _ in range(7)];hist=collections.Counter();nodes=0
# Process each vertex once, choosing all its missing neighbours among later
# vertices. This enumerates each labelled simple 2-regular graph once.
def visit(u):
 global nodes
 nodes+=1
 if nodes>100000:raise TimeoutError
 if u==7:
  assert all(len(ns)==2 for ns in g);todo=set(range(7));sizes=[]
  while todo:
   stack=[min(todo)];component=set()
   while stack:
    v=stack.pop()
    if v in component:continue
    component.add(v);stack.extend(g[v]-component)
   todo-=component;sizes.append(len(component))
  hist[tuple(sorted(sizes))]+=1;return
 need=2-len(g[u]);assert need>=0
 for chosen in itertools.combinations([v for v in range(u+1,7) if len(g[v])<2],need):
  for v in chosen:g[u].add(v);g[v].add(u)
  visit(u+1)
  for v in chosen:g[u].remove(v);g[v].remove(u)
visit(0);assert hist=={(7,):360,(3,4):105}
out={'status':'PASS','labelled_2regular_graphs':sum(hist.values()),'cycle_type_counts':{str(k):v for k,v in hist.items()},'nodes':nodes,'scope':'Exact auxiliary R cover if every high has singleton-empty sum3; this premise awaits the full min3 proof join.'}
(p/'cycle-results.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
