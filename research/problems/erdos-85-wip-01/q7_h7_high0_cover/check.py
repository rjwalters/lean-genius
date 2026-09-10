from pathlib import Path
import itertools,json
p=Path(__file__).parent
# Local indices0,1 are the two S0 vertices;2..7 are P01,...,P06.
def match(vs):
 if not vs:yield ();return
 for i in range(1,len(vs)):
  for rest in match(vs[1:i]+vs[i+1:]):yield ((vs[0],vs[i]),)+rest
allm=list(match(list(range(8))));assert len(allm)==105
representatives={};counts={}
for m in allm:
 canonical=min(tuple(sorted(tuple(sorted((perm[a],perm[b]))) for a,b in m)) for q in itertools.permutations(range(2,8)) for perm in [(0,1)+q,(1,0)+q])
 representatives[canonical]=canonical;counts[canonical]=counts.get(canonical,0)+1
assert sorted(counts.values())==[15,90]
names=['H'+str(c) for c in range(7)]+['S'+str(c)+s for c in range(7) for s in 'ab']+['P'+str(a)+str(b) for a,b in itertools.combinations(range(7),2)]+['E'+str(e) for e in range(7)];idx={v:i for i,v in enumerate(names)}
g=[set() for _ in names]
def add(graph,a,b):graph[idx[a]].add(idx[b]);graph[idx[b]].add(idx[a])
for c in range(7):
 for s in 'ab':add(g,'H'+str(c),'S'+str(c)+s)
for a,b in itertools.combinations(range(7),2):
 for c in [a,b]:add(g,'H'+str(c),'P'+str(a)+str(b))
local=['S0a','S0b']+['P0'+str(c) for c in range(1,7)];out=[]
for m in sorted(representatives):
 graph=[x.copy() for x in g]
 for a,b in m:add(graph,local[a],local[b])
 assert all(len(graph[a]&graph[b])<=1 for a,b in itertools.combinations(range(49),2))
 assert all(len(graph[v]&graph[idx['H0']])==1 for v in graph[idx['H0']])
 capacities={v:7-len(graph[idx[v]]) for v in local};assert sorted(capacities.values())==[4]*6+[5]*2 and sum(capacities.values())==34
 outside=[names[v] for v in range(7,49) if v not in graph[idx['H0']]];assert len(outside)==34
 assert all(not graph[idx[v]]&graph[idx['H0']] for v in outside)
 out.append(dict(twins_adjacent=(0,1) in m,orbit_size=counts[m],local_edges=[[local[a],local[b]] for a,b in m],slot_capacities=capacities,unassigned_low=outside,adjacency=[sorted(x) for x in graph]))
(p/'results.json').write_text(json.dumps(dict(local_matchings=105,group_size=1440,names=names,patterns=out,scope='Necessary H7 high0 neighbourhood cover and34 outside-low host slots; no empty graph selected, no completion/exclusion.'),indent=2)+'\n')
print('105 local matchings ->2orbits15/90; two C4-free49vertex seeds;34slots capacities5,5,4,4,4,4,4,4')
