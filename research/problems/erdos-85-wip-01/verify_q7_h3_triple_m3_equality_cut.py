"""Exact finite induced-graph exclusion of the H3 triple m3,T11 case. No optimizer or timeout."""
from itertools import combinations,permutations
from collections import Counter
from pathlib import Path
import json
matchings=[]
for missing in range(5):
 rest=[i for i in range(5) if i!=missing];a=rest[0]
 for b in rest[1:]:
  c,d=[i for i in rest if i not in [a,b]];matchings.append([(a,b),(c,d)])
assert len(matchings)==15

def add(adj,u,v):
 nu=adj[u];nv=adj[v]
 while nu:
  bit=nu&-nu;nu-=bit
  if adj[bit.bit_length()-1]&nv:return False
 adj[u]|=1<<v;adj[v]|=1<<u;return True
counts=Counter();examples={};checked=0;configs=[]
for pi in permutations(range(5)):
 base=[0]*15
 for i in range(5):
  assert add(base,i,5+i) and add(base,i,10+i) and add(base,5+i,10+pi[i])
 for m0 in matchings:
  a=base.copy()
  if not all(add(a,u,v) for u,v in m0):continue
  for m1 in matchings:
   b=a.copy()
   if not all(add(b,5+u,5+v) for u,v in m1):continue
   for m2 in matchings:
    c=b.copy();checked+=1
    if not all(add(c,10+u,10+v) for u,v in m2):continue
    triangles=sum(bool(c[u]>>v&1) and bool(c[u]>>w&1) and bool(c[v]>>w&1) for u,v,w in combinations(range(15),3))
    counts[triangles]+=1
    if triangles<=2:configs.append({"permutation":pi,"matchings":[m0,m1,m2],"triangles":triangles})
    examples.setdefault(str(triangles),{'permutation':pi,'matchings':[m0,m1,m2],'edges':[(u,v) for u in range(15) for v in range(u+1,15) if c[u]>>v&1]})

assert len(configs)==4680
assert Counter(c["triangles"] for c in configs)=={0:480,1:3480,2:720}

from pathlib import Path
from itertools import permutations
from collections import Counter
import json
base=Path(__file__).parent;configs=configs;labels=list(permutations(range(5)))
def encode(pi,ms):return tuple(pi)+tuple(v for m in ms for e in sorted(tuple(sorted(e)) for e in m) for v in e)
values={encode(c['permutation'],c['matchings']):c for c in configs};unseen=set(values);reps=[]
while unseen:
 key=min(unseen);c=values[key];pi=c['permutation'];ms=c['matchings'];maps={(0,1):list(range(5)),(0,2):list(range(5)),(1,2):pi}
 for (a,b),f in list(maps.items()):maps[b,a]=[f.index(i) for i in range(5)]
 orbit=set()
 for aa,bb,cc in permutations(range(3)):
  f=maps[aa,bb];g=maps[aa,cc];h=maps[bb,cc];invf=[f.index(i) for i in range(5)];invg=[g.index(i) for i in range(5)]
  ren=[list(range(5)),invf,invg];oldblocks=[aa,bb,cc]
  p=[invg[h[f[i]]] for i in range(5)]
  mm=[[(ren[j][u],ren[j][v]) for u,v in ms[old]] for j,old in enumerate(oldblocks)]
  for rho in labels:
   pp=[0]*5
   for i in range(5):pp[rho[i]]=rho[p[i]]
   orbit.add(encode(pp,[[(rho[u],rho[v]) for u,v in m] for m in mm]))
 assert orbit<=set(values)
 assert orbit<=unseen  # full disjoint orbits of the normalized configuration set
 unseen-=orbit;reps.append(dict(c,orbit_size=len(orbit)))
print('colored orbits',len(reps),'by triangles',dict(Counter(r['triangles'] for r in reps)),'total',sum(r['orbit_size'] for r in reps),flush=True)

assert len(reps)==14 and sum(r["orbit_size"] for r in reps)==4680

import json,time
from pathlib import Path
from itertools import combinations,permutations
base=Path(__file__).parent;reps=reps;examples={}
for ri,r in enumerate(reps):
 edges=[(i,5+i) for i in range(5)]+[(i,10+i) for i in range(5)]+[(5+i,10+r['permutation'][i]) for i in range(5)]+[(5*k+u,5*k+v) for k,m in enumerate(r['matchings']) for u,v in m]
 examples[str(ri)]={'edges':edges,'triangles':r['triangles']}
start=time.monotonic()

def add(adj,u,v):
 nu=adj[u];nv=adj[v]
 while nu:
  bit=nu&-nu;nu-=bit
  if adj[bit.bit_length()-1]&nv:return False
 newtri=(adj[u]&adj[v]).bit_count()
 if adj[24]+newtri>5:return False
 adj[24]+=newtri;adj[u]|=1<<v;adj[v]|=1<<u;return True
out={'scope':'Exact induced E24 necessary-condition enumeration for H3 triple m3,T11; no other equality case or profile excluded','attempts':[]}
for label in examples:
 example=examples[label]
 adj=[0]*25
 for u,v in example['edges']:assert add(adj,u,v)
 # U=0..14; N=15..20; T=21,22; distinguished u=23.
 fixed=[(23,n) for n in range(15,21)]+[(15,16),(17,18),(19,20),(21,22)]
 for u,v in fixed:assert add(adj,u,v)
 block_options=[]
 for block in range(3):
  U=list(range(5*block,5*block+5));special=next(v for v in U if adj[v].bit_count()==2);ordinary=[v for v in U if v!=special];options=[]
  for missing in combinations(range(15,21),2):
   R=[v for v in range(15,23) if v not in missing]
   for doubled in combinations(R,2):
    if all(v<21 for v in doubled):continue
    rest=[v for v in R if v not in doubled]
    for perm in permutations(rest):
     edges=[(special,v) for v in doubled]+list(zip(ordinary,perm));a=adj.copy()
     if all(add(a,u,v) for u,v in edges):options.append((set(missing),edges))
  block_options.append(options)
 print('fixture',label,'options',list(map(len,block_options)),flush=True)
 found=None;checks=0
 def dfs(block,a,missing,chosen):
  global found,checks
  if block==3:
   covered=set()
   for u,v,w in combinations(range(24),3):
    if a[u]>>v&1 and a[u]>>w&1 and a[v]>>w&1:covered.update([u,v,w])
   for g in range(3):
    for u in range(5*g,5*g+5):
     if any(a[u]>>v&1 for v in range(5*g,5*g+5)):covered.add(u)
   if 24-len(covered)>2*(5-a[24]):return False
   found=a;return True
  for ms,edges in block_options[block]:
   if missing&ms:continue
   checks+=1;b=a.copy()
   if all(add(b,u,v) for u,v in edges) and dfs(block+1,b,missing|ms,chosen+[edges]):return True
  return False
 dfs(0,adj,set(),[])
 entry={'fixture':label,'options':list(map(len,block_options)),'checks':checks,'found':found is not None,'timed_out':False}
 if found is not None:
  edges=[(u,v) for u in range(24) for v in range(u+1,24) if found[u]>>v&1]
  assert len(edges)==49 and sorted(v.bit_count() for v in found[:24])==[4]*23+[6]
  assert all((found[u]&found[v]).bit_count()<=1 for u in range(24) for v in range(u+1,24))
  entry['edges']=edges;entry['triangles']=found[24];print('EXACT E24 fixture PASS',label,flush=True)
 out['attempts'].append(entry)
 if found is not None:break
assert len(out['attempts'])==14 and not any(a['found'] for a in out['attempts'])
out['normalization']={'configurations':4680,'colored_orbits':14}
out['elapsed']=time.monotonic()-start;(base/'q7_h3_triple_m3_equality_cut.json').write_text(json.dumps(out,indent=2)+'\n');print('finished',out['elapsed'],flush=True)
