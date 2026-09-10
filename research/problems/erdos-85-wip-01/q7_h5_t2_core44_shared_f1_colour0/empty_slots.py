"""Exhaust the sixty colour0 empty-slot assignments per conditional skeleton."""
import pathlib,json,itertools
P=pathlib.Path(__file__).parent;results=[]
for row in json.loads((P/'skeletons.json').read_text())['results']:
 base=list(map(set,row['adjacency']));available=[e for e in range(11,23) if not base[e]&base[0]];tried=0;survivors=[]
 assert len(available)==5
 for f0pair in itertools.combinations(available,2):
  for singles in itertools.permutations([e for e in available if e not in f0pair]):
   tried+=1;g=[set(ns) for ns in base]
   for v,es in [(27,f0pair),(32,[singles[0]]),(33,[singles[1]]),(34,[singles[2]])]:
    for e in es:g[v].add(e);g[e].add(v)
   if any(len(g[u]&g[v])>1 for u,v in itertools.combinations(range(49),2)):continue
   assert all(len(g[v]&g[0])==1 for v in range(1,49))
   survivors.append(dict(f0pair=f0pair,g_empty=singles,adjacency=[sorted(ns) for ns in g]))
 assert tried==60
 results.append(dict(omitted=row['omitted'],internal=row['internal'],tried=tried,survivors=survivors))
 print(row['omitted'],row['internal'],tried,len(survivors))
(P/'empty-slot-results.json').write_text(json.dumps(dict(results=results,scope='Conditional colour0 slot layer only; no remaining edges or whole-core claim.'),indent=2)+'\n')
