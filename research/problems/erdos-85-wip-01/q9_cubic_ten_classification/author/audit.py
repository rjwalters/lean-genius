from pathlib import Path
from itertools import combinations
import json
p=Path(__file__).resolve().parent

def graph(edges):
 g=[set() for _ in range(10)]
 for a,b in edges:assert a!=b and b not in g[a];g[a].add(b);g[b].add(a)
 assert all(len(n)==3 for n in g)
 assert all(len(g[a]&g[b])<=1 for a,b in combinations(range(10),2))
 triangles=[list(v) for v in combinations(range(10),3) if all(b in g[a] for a,b in combinations(v,2))]
 return {'edges':[list(e) for e in sorted(tuple(sorted(e)) for e in edges)],'triangles':triangles}
first=[(0,i) for i in (1,2,3)]+[(i,3+i) for i in (1,2,3)]+[(i,6+i) for i in (1,2,3)]+[(i,4+(i-3)%6) for i in range(4,10)]
second=[(0,1),(1,2),(2,0),(6,7),(7,8),(8,6)]+[(i,i+3) for i in range(3)]+[(i+3,i+6) for i in range(3)]+[(i+3,9) for i in range(3)]
third=[(0,1),(1,2),(2,0)]+[(i,i+3) for i in range(3)]+[(6,7),(7,8),(8,9),(3,6),(3,7),(4,6),(4,9),(5,8),(5,9)]
reps=[graph(e) for e in (first,second,third)];assert [len(r['triangles']) for r in reps]==[0,2,3]
# Check the only three possible 3-edge remainder types on4 vertices.
remaining={'path':[(0,1),(1,2),(2,3)],'star':[(0,1),(0,2),(0,3)],'triangle':[(0,1),(1,2),(0,2)]};local={}
for name,edges in remaining.items():
 adj=[set() for _ in range(4)]
 for a,b in edges:adj[a].add(b);adj[b].add(a)
 targets=[3-len(n) for n in adj];solutions=[]
 for pairs in combinations(list(combinations(range(4),2)),3):
  if [sum(v in pair for pair in pairs) for v in range(4)]!=targets:continue
  if any(adj[a]&adj[b] for a,b in pairs):continue
  solutions.append(pairs)
 local[name]=solutions
assert local['path']==[((0,1),(0,3),(2,3))] and local['star']==[] and local['triangle']==[((0,3),(1,3),(2,3))]
(p/'representatives.json').write_text(json.dumps(reps,indent=2)+'\n');out={'status':'PASS','representatives':3,'triangle_counts':[0,2,3],'remainder_pair_solutions':local,'scope':'explicit representative and local remainder arithmetic; completeness proof separate'};(p/'results.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
