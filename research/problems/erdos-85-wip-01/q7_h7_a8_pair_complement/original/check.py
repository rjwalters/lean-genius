from pathlib import Path
import itertools,collections,json,math
p=Path(__file__).parent
edges=list(itertools.combinations(range(7),2));hist=collections.Counter();examples={};total=0
for es in itertools.combinations(edges,5):
 total+=1;g=[set() for _ in range(7)]
 for u,v in es:g[u].add(v);g[v].add(u)
 if not all(1<=len(ns)<=3 for ns in g):continue
 pattern=sorted(map(len,g));assert pattern in [[1]*5+[2,3],[1]*4+[2]*3]
 unseen=set(range(7));components=[]
 while unseen:
  todo=[min(unseen)];component=set()
  while todo:
   u=todo.pop()
   if u in component:continue
   component.add(u);todo.extend(g[u]-component)
  unseen-=component
  components.append((len(component),sum(len(g[u]) for u in component)//2,tuple(sorted(len(g[u]) for u in component))))
 signature=str(sorted(components));hist[signature]+=1;examples.setdefault(signature,es)
expected=sorted([1260,420,1260,1260,105]);assert total==math.comb(21,5)==20349 and sorted(hist.values())==expected and len(hist)==5
out={'status':'PASS','labelled_5edge_graphs_checked':total,'retained':sum(hist.values()),'classes':[{'component_signature':s,'labelled_count':n,'example_edges':examples[s]} for s,n in sorted(hist.items())],'scope':'Conditional a8 complement cover using reviewed exclusion of every s_i=1 host assignment and singleton empty degree<=2. No new host-assignment exclusion.'}
(p/'results.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
