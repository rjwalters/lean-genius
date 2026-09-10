import pathlib,json,hashlib,itertools,collections
P=pathlib.Path('/tmp/erdos85-sol1-h7-high0-cover');O=pathlib.Path(__file__).parent
pins=json.loads((P/'pins.json').read_text());assert all(hashlib.sha256((P/f).read_bytes()).hexdigest()==h for f,h in pins.items())
r=json.loads((P/'results.json').read_text());edges=list(itertools.combinations(range(8),2));matchings=set()
for group in itertools.combinations(edges,4):
 if sorted(v for e in group for v in e)==list(range(8)):matchings.add(tuple(sorted(group)))
assert len(matchings)==105
# Orbit closure under generators, no minimization over the full action.
gens=[(0,1)]+[(i,i+1) for i in range(2,7)];left=set(matchings);orbits=[]
while left:
 orbit={min(left)};todo=list(orbit)
 while todo:
  m=todo.pop()
  for a,b in gens:
   trans=lambda v:b if v==a else a if v==b else v
   n=tuple(sorted(tuple(sorted((trans(u),trans(v)))) for u,v in m))
   if n not in orbit:orbit.add(n);todo.append(n)
 assert orbit<=matchings;left-=orbit;orbits.append(orbit)
assert sorted(map(len,orbits))==[15,90]
names=r['names'];ix={n:i for i,n in enumerate(names)};local=['S0a','S0b']+['P0'+str(c) for c in range(1,7)]
audit=[]
for seed in r['patterns']:
 m=tuple(sorted(tuple(sorted((local.index(a),local.index(b)))) for a,b in seed['local_edges']))
 orbit=next(s for s in orbits if m in s);assert len(orbit)==seed['orbit_size']
 g=[set() for _ in names]
 def add(a,b):g[ix[a]].add(ix[b]);g[ix[b]].add(ix[a])
 for name in names[7:]:
  if name.startswith('S'):add('H'+name[1],name)
  elif name.startswith('P'):
   for c in name[1:]:add('H'+c,name)
 for a,b in seed['local_edges']:add(a,b)
 assert [sorted(s) for s in g]==seed['adjacency']
 assert all(len(g[u]&g[v])<=1 for u,v in itertools.combinations(range(49),2))
 N=g[0];assert N=={ix[n] for n in local} and len(N)==8
 assert all(len(g[v]&N)==1 for v in N)
 outside=set(range(7,49))-N;assert len(outside)==34 and all(not g[v]&N for v in outside)
 cap={names[v]:7-len(g[v]) for v in N};assert cap==seed['slot_capacities'] and sum(cap.values())==34
 assert set(seed['unassigned_low'])=={names[v] for v in outside}
 audit.append({'twins_adjacent':seed['twins_adjacent'],'orbit_size':len(orbit),'guests':len(outside),'capacity':sum(cap.values())})
assert all(hashlib.sha256((P/f).read_bytes()).hexdigest()==h for f,h in pins.items())
res={'review':2064,'status':'PASS','matchings':105,'orbit_sizes':sorted(map(len,orbits)),'seeds':audit,'pins':pins,'scope':'Necessary high0 host cover only; no H7 branch exclusion','semantic_audit':'BC gives exactly one neighbour inside N(H0) to each of its members; hence perfect matching. Any whole-colour permutation fixing0 and independent swap of the two S0 vertices preserves support classes and acts on full graphs, so the local orbit quotient is legitimate. Each outside low vertex needs exactly one N(H0) neighbour. High-neighbour degrees and matching already account for2 or3 edges, leaving exact5/4 guest capacities. High vertices outside0 already have their unique N(H0) neighbour P0j and require no guest slot. No extra fixed outside-low to host edges exist initially.'}
(O/'REVIEW2064.json').write_text(json.dumps(res,indent=2)+'\n');print(json.dumps(res))
