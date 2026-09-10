"""Exact classification of the induced seven-vertex equality case only.
Enumerates fixed nine-edge subsets and checks membership in two S7 orbits.
No H7 graph search, optimizer, or whole-profile exclusion.
"""
from itertools import combinations, permutations
from collections import Counter
from math import comb
from pathlib import Path
import json
pairs=list(combinations(range(7),2));index={e:i for i,e in enumerate(pairs)}
representatives=[[(0,1),(0,2),(0,3),(1,2),(1,4),(2,5),(3,6),(4,6),(5,6)],[(0,1),(0,2),(0,3),(1,2),(1,4),(3,5),(3,6),(4,5),(5,6)]]
orbits=[]
for edges in representatives:
 orbit={sum(1<<index[tuple(sorted((perm[u],perm[v])))] for u,v in edges) for perm in permutations(range(7))}
 orbits.append(orbit)
assert [len(v) for v in orbits]==[840,2520] and not (orbits[0]&orbits[1])
all_orbits=orbits[0]|orbits[1]
counts=Counter();examples={};valid=0;checked=0
for edges in combinations(pairs,9):
 checked+=1
 deg=[0]*7;ns=[0]*7
 for u,v in edges:deg[u]+=1;deg[v]+=1;ns[u]|=1<<v;ns[v]|=1<<u
 if max(deg)>3:continue
 if any((ns[u]&ns[v]).bit_count()>1 for u,v in pairs):continue
 triangles=sum(bool(ns[u]>>v&1) and bool(ns[u]>>w&1) and bool(ns[v]>>w&1) for u,v,w in combinations(range(7),3))
 assert sum(1<<index[e] for e in edges) in all_orbits
 key=(tuple(sorted(deg)),triangles);counts[key]+=1;examples.setdefault(str(key),edges);valid+=1
assert checked==comb(21,9)==293930 and valid==len(all_orbits)
assert set(counts)=={((2,2,2,3,3,3,3),1),((2,2,2,3,3,3,3),2)}
out={'scope':'Exhaustive labeled7-vertex9-edge simple graphs of maximumdegree3 and C4free only, not H7 graphs','edge_sets_checked':checked,'representative_orbit_sizes':[len(v) for v in orbits],'representatives':representatives,'valid_labeled_graphs':valid,'counts':{str(k):v for k,v in counts.items()},'examples':examples}
Path(__file__).with_name('q7_seven_vertex_nine_edge_classification.json').write_text(json.dumps(out,indent=2)+'\n')
print(out)
