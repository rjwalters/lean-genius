"""Regenerate normalized H3 pair cores with P0 adjacent to P1."""
from itertools import combinations, permutations, product
from pathlib import Path
import json

def generate():
 colors=[[4,5,8,9,10,11],[3,6,12,13,14,15],[7,16,17,18,19,20]]
 matchings=[[(0,j),tuple(x for x in range(1,4) if x!=j)] for j in range(1,4)]
 groups=[]
 for same in [True,False]:
  m0,m1=1,2 if same else 3
  for eps in [0,1]:
   base=[(0,1),(0,3),(1,4),(2,5),(2,6),(2,7),(5,16+m0),(6,16+m1),(7,16),(17,18),(19,20)]
   for i in range(3):base.extend((21+i,v) for v in [a for a in range(3) if a!=i]+colors[i])
   for i,m in [(0,m0),(1,m1)]:base.extend((8+4*i+j,16+v) for j,v in enumerate(x for x in range(5) if x!=m))
   accepted=[];checked=0
   for M0,M1 in product(matchings,repeat=2):
    fixed=base+[(8+u,8+v) for u,v in M0]+[(12+u,12+v) for u,v in M1]
    cross=[]
    if eps:
     for ps in permutations(range(4)):cross.append([(3,4)]+[(8+u,12+v) for u,v in enumerate(ps)])
    else:
     for a,b in product(range(4),repeat=2):
      for ps in permutations([v for v in range(4) if v!=b]):cross.append([(3,8+a),(4,12+b)]+[(8+u,12+v) for u,v in zip([u for u in range(4) if u!=a],ps)])
    for ce in cross:
     checked+=1;edges=fixed+ce;adj=[set() for _ in range(24)]
     assert len(edges)==52 and len({tuple(sorted(e)) for e in edges})==52
     for u,v in edges:adj[u].add(v);adj[v].add(u)
     if any(len(adj[u]&adj[v])>1 for u,v in combinations(range(24),2)):continue
     assert [len(x) for x in adj]==[4,4,5]+[3]*5+[4]*13+[8]*3
     hosts=[[s for s in colors[i] if not(adj[i]&adj[s])] for i in range(3)]
     assert list(map(len,hosts))==[4,4,3]
     triples=[t for t in product(*colors) if all(not(adj[u]&adj[v]) for u,v in combinations(t,2))]
     accepted.append({'edges':edges,'colors':colors,'hosts':hosts,'triples':triples})
   assert checked==(216 if eps else 864)
   assert len(accepted)==(0 if eps else (36 if same else 39))
   groups.append({'same_edge':same,'epsilon':eps,'checked':checked,'accepted':accepted})
 return groups


from math import comb
def solve(core,k,ci,hi):
 hosts=list(product(*(list(combinations(h,n)) for h,n in zip(core['hosts'],[3,3,2]))))[hi]
 ts=core['triples'];pm=[sum(1<<(24*min(u,v)+max(u,v)) for u,v in combinations(t,2)) for t in ts]
 need=[0]*24
 for v in range(3,21):need[v]=4 if v<8 else 3
 for v in sum((list(h) for h in hosts),[]):need[v]-=1
 nodes=0;leaves=0;found=None;timed_out=False
 enodes=0;eleaves=0;full_graph=None
 
 def allowed(a,u,v):
  if a[u]>>v&1:return False
  bits=a[u]
  while bits:
   bit=bits&-bits;bits-=bit
   if a[bit.bit_length()-1]&a[v]:return False
  return True
 
 def empty_dfs(a,rem):
  nonlocal enodes,eleaves,full_graph
  enodes+=1
  active=[v for v in range(24,49) if rem[v-24]]
  if not active:
   eleaves+=1
   assert [a[v].bit_count() for v in range(49)]==[7]*21+[8]*3+[7]*25
   assert all((a[u]&a[v]).bit_count()<=1 for u,v in combinations(range(49),2))
   full_graph=[(u,v) for u,v in combinations(range(49),2) if a[u]>>v&1];return True
  opts=[]
  for u in active:
   vs=[v for v in active if v!=u and allowed(a,u,v)]
   if len(vs)<rem[u-24]:return False
   opts.append((comb(len(vs),rem[u-24]),u,vs))
  _,u,vs=min(opts,key=lambda x:x[0]);degree=rem[u-24]
  for chosen in combinations(vs,degree):
   aa=a.copy();rr=rem.copy();ok=True
   for v in chosen:
    if not allowed(aa,u,v):ok=False;break
    aa[u]|=1<<v;aa[v]|=1<<u;rr[v-24]-=1
   if not ok:continue
   rr[u-24]=0
   if empty_dfs(aa,rr):return True
  return False
 
 
 def leaf(chosen):
  nonlocal leaves,found
  leaves+=1;a=[0]*49
  def add(u,v):a[u]|=1<<v;a[v]|=1<<u
  for u,v in core['edges']:add(u,v)
  for color,ss in enumerate(hosts):
   for j,s in enumerate(ss):v=24+[0,3,6][color]+j;add(v,color);add(v,s)
  for i,j in enumerate(chosen):
   for s in ts[j]:add(32+i,s)
  assert len(chosen)==17
  assert [a[v].bit_count() for v in range(24)]==[7]*21+[8]*3
  assert all((a[u]&a[v]).bit_count()<=1 for u,v in combinations(range(49),2))
  allowed=[];degrees=[0]*25
  for u,v in combinations(range(24,49),2):
   bits=a[u];neigh=0
   while bits:
    bit=bits&-bits;bits-=bit;neigh|=a[bit.bit_length()-1]
   if not(neigh&a[v]):allowed.append((u,v));degrees[u-24]+=1;degrees[v-24]+=1
  required=[5]*8+[4]*17
  if any(x<y for x,y in zip(degrees,required)):return False
  for u in range(24,49):
   candidates=[v if x==u else x for x,v in allowed if x==u or v==u]
   if not any(all(not(a[v]&a[w]) for v,w in combinations(choice,2)) for choice in combinations(candidates,required[u-24])):return False
  if not empty_dfs(a,[5]*8+[4]*17):return False
  found={'chosen_triples' :[ts[j] for j in chosen],'hosts':hosts,'base_edges':[(u,v) for u,v in combinations(range(49),2) if a[u]>>v&1],'allowed_empty_edges':allowed,'allowed_empty_degrees':degrees}
  return True
 
 def dfs(demand,used,chosen):
  nonlocal nodes
  nodes+=1
  if not any(demand):return leaf(chosen)
  avail=[j for j,t in enumerate(ts) if not(pm[j]&used) and all(demand[v]>0 for v in t)]
  opts=[]
  for v in range(3,21):
   d=demand[v]
   if not d:continue
   choices=[j for j in avail if v in ts[j]]
   if len(choices)<d:return False
   opts.append((comb(len(choices),d),v,choices))
  _,v,choices=min(opts,key=lambda x:x[0]);d=demand[v]
  for batch in combinations(choices,d):
   ps=used;nd=demand.copy();ok=True
   for j in batch:
    if pm[j]&ps:ok=False;break
    ps|=pm[j]
    for u in ts[j]:
     nd[u]-=1
     if nd[u]<0:ok=False;break
    if not ok:break
   if ok and dfs(nd,ps,chosen+list(batch)):return True
  return False
 dfs(need,0,[])
 return {"shape":k,"core_index":ci,"host_index":hi,"nodes":nodes,"leaves":leaves,"empty_nodes":enodes,"empty_leaves":eleaves,"found":found is not None,"full_graph":full_graph}

rows=[]
for k,group in enumerate(generate()[::2]):
 for ci,core in enumerate(group['accepted']):
  for hi in range(48):
   rows.append(solve(core,k,ci,hi))
   if len(rows)%100==0:print('completed',len(rows),flush=True)
assert len(rows)==3600
assert all(not r['found'] for r in rows)
Path(__file__).with_name('q7_h3_pair_b1_full_exclusion.json').write_text(json.dumps({'scope':'H3 pair b1 full completion','cases':rows},indent=2)+'\n')
print('All3600 cases exhausted; zero graphs',flush=True)
