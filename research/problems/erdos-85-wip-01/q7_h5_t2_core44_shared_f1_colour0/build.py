"""Canonical completion of the colour0 singleton slots, before empty incidences."""
import pathlib,json,itertools
P=pathlib.Path(__file__).parent;S=P
rows=[]
for branch in json.loads((S/'branches.json').read_text())['results']:
 key=(branch['omitted'],tuple(map(tuple,branch['internal'])),branch['af'],branch['bf'])
 if not (branch['shared']==1 and branch['omitted']==7 and branch['internal']==[] and branch['af']==4 and branch['bf']==2):continue
 g=list(map(set,branch['adjacency']))+[set() for _ in range(3)]
 def edge(u,v):g[u].add(v);g[v].add(u)
 for v in [32,33,34]:edge(v,0)
 for u,v in [(27,32),(28,33),(33,34),(30,34)]:edge(u,v)
 slots=[]
 for c in range(1,5):
  for host in [23,24,27,32,33,34]:
   if g[c]&g[host]:continue
   v=len(g);g.append(set());edge(v,c);edge(v,host);slots.append(dict(vertex=v,colour=c,host=host))
 assert len(g)==49
 violations=[(u,v) for u,v in itertools.combinations(range(49),2) if len(g[u]&g[v])>1]
 assert not violations,(key,violations)
 assert [sum(x['colour']==c for x in slots) for c in range(1,5)]==[4,3,4,3]
 for v in range(35,49):assert len(g[v]&g[0])==1
 rows.append(dict(omitted=branch['omitted'],internal=branch['internal'],af=branch['af'],bf=branch['bf'],slots=slots,adjacency=[sorted(ns) for ns in g]))
assert len(rows)==1
(P/'skeletons.json').write_text(json.dumps(dict(results=rows,scope='One conditional colour0 slot-labelled 49vertex partial skeletons; F-star and ordinary empty edges, other singleton edges absent. No exclusion.'),indent=2)+'\n')
print('PASS: one C4-free 49vertex skeletons, fourteen unique colour0 host slots each')
