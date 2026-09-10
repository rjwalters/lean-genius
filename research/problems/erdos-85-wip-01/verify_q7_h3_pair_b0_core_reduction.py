"""Exact normalized nonempty cores for the H3 pair profile with independent P.
No full-profile exclusion or empty-graph realization is claimed.
"""
from itertools import combinations,permutations,product
from pathlib import Path
import json
pairs=list(combinations(range(3),2));results=[]
def X(i,a):return 3+3*i+a
def O(i,v):return 12+3*i+v
for k in range(4):
 eps=set(pairs[:k]);missing={};base=[]
 for i in range(3):
  absent=[j for j in range(3) if j!=i and tuple(sorted((i,j))) not in eps]
  missing[i]={j:v+1 for v,j in enumerate(absent)}
  base.extend([(21+i,a) for a in range(3) if a!=i]+[(21+i,X(i,a)) for a in range(3)]+[(21+i,O(i,v)) for v in range(3)])
  base.extend([(i,X(j,i)) for j in range(3)])
  base.extend([(O(i,1),O(i,2)),(X(i,i),O(i,0))])
  for j,v in missing[i].items():base.append((X(j,i),O(i,v)))
 for i,j in eps:base.append((X(i,j),X(j,i)))
 opts=[]
 for i,j in pairs:
  left=[v for v in range(3) if v!=missing[i].get(j,-1)];right=[v for v in range(3) if v!=missing[j].get(i,-1)]
  opts.append([[(O(i,u),O(j,v)) for u,v in zip(left,ps)] for ps in permutations(right)])
 accepted=[];checked=0
 for cross in product(*opts):
  checked+=1;edges=base+sum(cross,[]);a=[set() for _ in range(24)]
  assert len(edges)==51 and len({tuple(sorted(e)) for e in edges})==51
  for u,v in edges:a[u].add(v);a[v].add(u)
  if any(len(a[u]&a[v])>1 for u,v in combinations(range(24),2)):continue
  assert [len(a[v]) for v in range(24)]==[5]*3+[3]*9+[4]*9+[8]*3
  assert all(2<=len(a[u]&set(range(12,21)))<=3 for u in range(12,21))
  assert sum(len(a[u]&set(range(12,21))) for u in range(12,21))==2*(9+k)
  colors=[[X(i,j) for j in range(3)]+[O(i,j) for j in range(3)] for i in range(3)]
  hosts=[[s for s in colors[i] if not(a[i]&a[s])] for i in range(3)]
  assert all(len(h)==3 for h in hosts)
  triples=[t for t in product(*colors) if all(not(a[u]&a[v]) for u,v in combinations(t,2))]
  accepted.append({'edges':edges,'pair_empty_singleton_hosts':hosts,'ordinary_empty_singleton_triples':triples,'O_triangles':[list(t) for t in combinations(range(12,21),3) if all(v in a[u] for u,v in combinations(t,2))]})
 assert checked==[8,24,72,216][k]
 assert len(accepted)==[5,7,8,16][k]
 results.append({'epsilon_edges':sorted(eps),'checked':checked,'accepted':accepted})
assert sum(r['checked'] for r in results)==320
assert sum(len(r['accepted']) for r in results)==36
Path(__file__).with_name('q7_h3_pair_b0_core_reduction.json').write_text(json.dumps({'scope':'Complete normalized known nonempty cores for H3 pair b0; no full realization or exclusion','cases':results},indent=2)+'\n')
print('PASS320 normalized choices,36 C4-free cores; each P has3 singleton hosts; no full-profile exclusion')
