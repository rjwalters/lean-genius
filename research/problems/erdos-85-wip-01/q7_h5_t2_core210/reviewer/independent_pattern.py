from pathlib import Path
import json,itertools,hashlib
S=[{0,1,2},{0,3,4},{1,3},{1,4},{2,3},{2,4}];es={(0,2),(0,5),(1,3),(1,4)};mask=sum(1<<i for i,e in enumerate(itertools.combinations(range(6),2)) if e in es);assert mask==210
g=[set() for _ in range(11)]
for i,s in enumerate(S):
 for c in s:g[c].add(5+i);g[5+i].add(c)
for i,j in es:g[5+i].add(5+j);g[5+j].add(5+i)
assert all(g[u]&g[v] for u,v in itertools.combinations(range(5,11),2))
dem=[]
for v in range(5,11):
 counts=[len(g[v]&g[c]) for c in range(5)];assert all(x<=1 for x in counts)
 dem.append(7-len(g[v])-counts.count(0))
assert dem==[1,1,2,2,2,2]
rows=[[i] for i,n in enumerate(dem) for _ in range(n)]+[[],[]];degrees=[2+sum(len(S[i])-1 for i in r) for r in rows]
p=Path(__file__).parent;author=json.loads((p/'core210-pattern.json').read_text())[0];assert author['patterns']==[{'heavy_rows':rows,'empty_degrees':degrees}]
result={'status':'PASS','core':210,'heavy_empty_demands':dem,'empty_degrees':degrees,'unique_pattern_up_to_empty_labels':True,'reason':'Every pair of heavy vertices already has a common neighbour in full11vertex graph, so no empty can host two. Degree demand fixes multiplicities; unassigned rows have no heavy guest.'}
(p/'independent-pattern-results.json').write_text(json.dumps(result,indent=2)+'\n');print(result)
