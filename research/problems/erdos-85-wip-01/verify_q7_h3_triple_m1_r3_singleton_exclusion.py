"""Exact unrestricted H3 triple m1,r3 singleton-neighborhood exclusion."""
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
partial=[]
for missing_from in range(5):
 for missing_to in range(5):
  domain=[i for i in range(5) if i!=missing_from];codomain=[i for i in range(5) if i!=missing_to]
  for perm in permutations(codomain):
   pi=[-1]*5
   for i,j in zip(domain,perm):pi[i]=j
   partial.append(pi)
assert len(partial)==600
for pi in partial:
 base=[0]*15
 for i in range(5):
  assert add(base,i,5+i) and add(base,i,10+i) and (pi[i]<0 or add(base,5+i,10+pi[i]))
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
    if True:configs.append({"permutation":pi,"matchings":[m0,m1,m2],"triangles":triangles})
    examples.setdefault(str(triangles),{'permutation':pi,'matchings':[m0,m1,m2],'edges':[(u,v) for u in range(15) for v in range(u+1,15) if c[u]>>v&1]})

assert len(configs)==79650
labels=list(permutations(range(5)))
def encode(pi,ms):return tuple(pi)+tuple(v for m in ms for e in sorted(tuple(sorted(e)) for e in m) for v in e)
values={encode(c['permutation'],c['matchings']):c for c in configs};unseen=set(values);reps=[]
while unseen:
 key=min(unseen);c=values[key];pi=c['permutation'];ms=c['matchings'];maps={(0,1):list(range(5)),(0,2):list(range(5)),(1,2):pi}
 for (a,b),f in list(maps.items()):maps[b,a]=[f.index(i) if i in f else -1 for i in range(5)]
 orbit=set()
 for aa,bb,cc in [(0,1,2),(0,2,1)]:
  f=maps[aa,bb];g=maps[aa,cc];h=maps[bb,cc];invf=[f.index(i) if i in f else -1 for i in range(5)];invg=[g.index(i) for i in range(5)]
  ren=[list(range(5)),invf,invg];oldblocks=[aa,bb,cc]
  p=[invg[h[f[i]]] if h[f[i]]>=0 else -1 for i in range(5)]
  mm=[[(ren[j][u],ren[j][v]) for u,v in ms[old]] for j,old in enumerate(oldblocks)]
  for rho in labels:
   pp=[-1]*5
   for i in range(5):
    if p[i]>=0:pp[rho[i]]=rho[p[i]]
   orbit.add(encode(pp,[[(rho[u],rho[v]) for u,v in m] for m in mm]))
 assert orbit<=set(values)
 assert orbit<=unseen  # full disjoint orbits of the normalized configuration set
 unseen-=orbit;reps.append(dict(c,orbit_size=len(orbit)))
print('colored orbits',len(reps),'by triangles',dict(Counter(r['triangles'] for r in reps)),'total',sum(r['orbit_size'] for r in reps),flush=True)

U_reps=reps
assert len(U_reps)==370
from itertools import permutations,product,combinations
from pathlib import Path
from collections import Counter
import json
pairs=list(combinations(range(8),2));idx={e:i for i,e in enumerate(pairs)};out={}
for m in [1,2,3]:
 matching={(2*i,2*i+1) for i in range(m)}
 autos=[p for p in permutations(range(6)) if {tuple(sorted((p[u],p[v]))) for u,v in matching}==matching]
 configs={}
 for eps,a,b in product(range(2),range(-1,6),range(-1,6)):
  if int(a>=0)+eps<1 or int(b>=0)+eps<1:continue
  edges=set(matching)
  if eps:edges.add((6,7))
  if a>=0:edges.add((a,6))
  if b>=0:edges.add((b,7))
  if len(edges) not in [3,4]:continue
  adj=[set() for _ in range(9)]
  for u,v in edges|{(i,8) for i in range(6)}:adj[u].add(v);adj[v].add(u)
  if any(len(adj[u]&adj[v])>1 for u,v in combinations(range(9),2)):continue
  key=sum(1<<idx[e] for e in edges);configs[key]={'m':m,'r':len(edges),'epsilon':eps,'a':a,'b':b,'edges':sorted(edges),'U_degrees':[4-len(adj[v]) for v in range(8)]}
 unseen=set(configs);reps=[]
 while unseen:
  key=min(unseen);c=configs[key];orbit=set()
  for p in autos:
   for swap in [False,True]:
    perm=list(p)+([7,6] if swap else [6,7]);orbit.add(sum(1<<idx[tuple(sorted((perm[u],perm[v])))] for u,v in c['edges']))
  assert orbit<=unseen;unseen-=orbit;reps.append(dict(c,orbit_size=len(orbit)))
 print('m',m,'labeled',len(configs),'orbits',len(reps),'by r',dict(Counter(c['r'] for c in reps)),flush=True)
 out[str(m)]={'labeled':len(configs),'representatives':reps}

R_reps=[a for a in out["1"]["representatives"] if a["r"]==3]
assert len(R_reps)==7

def verify_case(R,U,ri,ui):
 m=1;r=3
 adj=[0]*25
 
 def add(a,u,v):
  nu=a[u];nv=a[v]
  while nu:
   bit=nu&-nu;nu-=bit
   if a[bit.bit_length()-1]&nv:return False
  tri=(a[u]&a[v]).bit_count()
  a[24]+=tri;a[u]|=1<<v;a[v]|=1<<u;return True
 edges=[(i,5+i) for i in range(5)]+[(i,10+i) for i in range(5)]+[(5+i,10+j) for i,j in enumerate(U['permutation']) if j>=0]+[(5*k+u,5*k+v) for k,ma in enumerate(U['matchings']) for u,v in ma]+[(u+15,v+15) for u,v in R['edges']]+[(23,v) for v in range(15,21)]
 for u,v in edges:assert add(adj,u,v)
 target=[4-adj[v].bit_count() for v in range(15,23)];assert all(0<=d<=3 for d in target)
 options=[]
 for block in range(3):
  vertices=sorted(range(5*block,5*block+5),key=lambda v:adj[v].bit_count());opts=[]
  def build(k,a,available,es):
   if k==5:
    selected=sum(1<<(v-15) for v in range(15,23) if v not in available and target[v-15]>0)
    if any(d==3 and not(selected>>j&1) for j,d in enumerate(target)):return
    opts.append((selected,es));return
   v=vertices[k];degree=4-adj[v].bit_count()
   for choice in combinations(available,degree):
    if sum(w<21 for w in choice)>1:continue
    aa=a.copy()
    if all(add(aa,v,w) for w in choice):build(k+1,aa,[w for w in available if w not in choice],es+[(v,w) for w in choice])
  build(0,adj.copy(),[v for v in range(15,23) if target[v-15]>0],[]);options.append(opts)
 order=sorted(range(3),key=lambda k:len(options[k]));buckets=[]
 for k in order:
  bucket={}
  for mask,es in options[k]:bucket.setdefault(mask,[]).append(es)
  buckets.append(bucket)
 print('case',m,r,ri,ui,'options',list(map(len,options)),flush=True);found=None;checks=0;leaves=0
 unmatched=set(range(15+2*m,21))
 def dfs(depth,a,remaining):
  nonlocal found,checks,leaves
  if depth==3:
   leaves+=1
   covers=[]
   for color in range(3):
    allowed=set(range(23))-set(range(5*color,5*color+5))
    triples=[t for t in combinations(sorted(allowed),3) if all(not(a[u]&a[v]) for u,v in combinations(t,2)) and all(sum(5*k<=v<5*k+5 for v in t)<=1 for k in range(3))]
    masks=[sum(1<<v for v in t) for t in triples]
    pairs=[sum(1<<(24*u+v) for u,v in combinations(t,2)) for t in triples]
    by_vertex={v:[j for j,t in enumerate(masks) if t>>v&1] for v in allowed};cs=[]
    def cover(left,ps,chosen):
     if not left:cs.append((ps,chosen));return
     opts=min(([j for j in by_vertex[v] if masks[j]&left==masks[j]] for v in allowed if left>>v&1),key=len)
     for j in opts:cover(left^masks[j],ps|pairs[j],chosen+[masks[j]])
    cover(sum(1<<v for v in allowed),0,[])
    if not cs:return False
    covers.append(cs)
   for p0,c0 in covers[0]:
    for p1,c1 in covers[1]:
     if p0&p1:continue
     for p2,c2 in covers[2]:
      if (p0|p1)&p2:continue
      ts=c0+c1+c2;ok=True
      for x,tx in enumerate(ts):
       neighbors=0;bits=tx
       while bits:
        bit=bits&-bits;bits-=bit;neighbors|=a[bit.bit_length()-1]
       for color in range(3):
        if not any(y!=x and not(neighbors&ts[y]) for y in range(6*color,6*color+6)):
         ok=False;break
       if not ok:break
      if ok:
       found=a;return True
   return False
  candidates=buckets[depth]
  if depth==2:
   if any(d not in [0,1] for d in remaining):return False
   mask=sum(1<<j for j,d in enumerate(remaining) if d);candidates={mask:candidates.get(mask,[])}
  for mask,ess in candidates.items():
   rem=[d-((mask>>j)&1) for j,d in enumerate(remaining)]
   if any(d<0 or d>2-depth for d in rem):continue
   for es in ess:
    checks+=1;aa=a.copy()
    if all(add(aa,u,v) for u,v in es) and dfs(depth+1,aa,rem):return True
  return False
 dfs(0,adj.copy(),target)
 
 return {"R_index":ri,"U_index":ui,"checks":checks,"leaves":leaves,"found":found is not None,"edges":None if found is None else [(u,v) for u,v in combinations(range(24),2) if found[u]>>v&1]}

results=[verify_case(R,U,ri,ui) for ri,R in enumerate(R_reps) for ui,U in enumerate(U_reps)]
assert len(results)==2590
assert not any(r["found"] for r in results)
Path(__file__).with_name("q7_h3_triple_m1_r3_singleton_exclusion.json").write_text(json.dumps({"scope":"Whole m1r3 unrestricted induced exclusion","cases":results},indent=2)+"\n")
print("All2590 cases exhausted; survivors",sum(r["found"] for r in results))
