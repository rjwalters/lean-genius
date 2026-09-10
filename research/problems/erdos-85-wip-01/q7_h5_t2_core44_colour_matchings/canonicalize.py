from pathlib import Path
import json,itertools,hashlib
p=Path(__file__).parent;d=json.loads((p/'results.json').read_text());names=d['names'];idx={n:i for i,n in enumerate(names)}
def mate(edges,v):return next(b if a==v else a for a,b in edges if v in (a,b))
allgraphs={};checked=0
for af,bf in itertools.product([3,4],[1,2]):
 for choice in itertools.product(*(r['allowed_matchings'] for r in d['profiles'])):
  perm={n:n for n in names}
  for c,fixed in [(0,'f0'),(1,'f1')]:
   gs=['g'+str(c)+s for s in 'abc'];first=mate(choice[c],fixed)
   for a,b in zip([first]+[v for v in gs if v!=first],gs):perm[a]=b
  first=mate(choice[2],'b2');perm[first]='g2a';perm[next(v for v in ['g2a','g2b'] if v!=first)]='g2b'
  direct=mate(choice[3],'f3')=='d3'
  if not direct:
   first=mate(choice[3],'f3');perm[first]='g3a';perm[next(v for v in ['g3a','g3b'] if v!=first)]='g3b'
  assert len(set(perm.values()))==37
  graph=list(map(set,d['base_adjacency']))
  for a,b in sum(choice,[])+[('f1','f3'),('a0','f'+str(af)),('b0','f'+str(bf))]:graph[idx[a]].add(idx[b]);graph[idx[b]].add(idx[a])
  mapped=[set() for _ in names]
  for a,ns in enumerate(graph):mapped[idx[perm[names[a]]]]={idx[perm[names[v]]] for v in ns}
  mapped=[sorted(ns) for ns in mapped];key=(af,bf,direct)
  if key in allgraphs:assert allgraphs[key]==mapped
  else:allgraphs[key]=mapped
  checked+=1
assert checked==216 and len(allgraphs)==8
out={'source_sha256':hashlib.sha256((p/'results.json').read_bytes()).hexdigest(),'labelled_configurations_checked':checked,'canonical_configurations':[{'af':a,'bf':b,'f3_d3_edge':c,'adjacency':g} for (a,b,c),g in sorted(allgraphs.items())],'names':names,'scope':'Explicit eight37vertex skeletons; every54 matching assignment peraf/bf checked under full-graph relabelling; no empties or fullgraph claim.'}
(p/'canonical-results.json').write_text(json.dumps(out,indent=2)+'\n')
print('216 labelled configurations mapped to exactly8 canonical graphs')
