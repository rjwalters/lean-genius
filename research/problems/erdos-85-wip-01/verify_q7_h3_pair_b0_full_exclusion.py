from math import comb
"""Exact normalized nonempty cores for the H3 pair profile with independent P.
Exhaustive empty-incidence and empty-edge completion for independent P.
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

core_cases=results
def solve(core,k,ci,hi):
 hosts=list(product(*(list(combinations(h,2)) for h in core['pair_empty_singleton_hosts'])))[hi]
 ts=core['ordinary_empty_singleton_triples'];pm=[sum(1<<(24*min(u,v)+max(u,v)) for u,v in combinations(t,2)) for t in ts]
 need=[0]*24
 for v in range(3,21):need[v]=4 if v<12 else 3
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
   for j,s in enumerate(ss):v=24+2*color+j;add(v,color);add(v,s)
  for i,j in enumerate(chosen):
   for s in ts[j]:add(30+i,s)
  assert len(chosen)==19
  assert [a[v].bit_count() for v in range(24)]==[7]*21+[8]*3
  assert all((a[u]&a[v]).bit_count()<=1 for u,v in combinations(range(49),2))
  allowed=[];degrees=[0]*25
  for u,v in combinations(range(24,49),2):
   bits=a[u];neigh=0
   while bits:
    bit=bits&-bits;bits-=bit;neigh|=a[bit.bit_length()-1]
   if not(neigh&a[v]):allowed.append((u,v));degrees[u-24]+=1;degrees[v-24]+=1
  required=[5]*6+[4]*19
  if any(x<y for x,y in zip(degrees,required)):return False
  for u in range(24,49):
   candidates=[v if x==u else x for x,v in allowed if x==u or v==u]
   if not any(all(not(a[v]&a[w]) for v,w in combinations(choice,2)) for choice in combinations(candidates,required[u-24])):return False
  if not empty_dfs(a,[5]*6+[4]*19):return False
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
 return {"epsilon_count":k,"core_index":ci,"host_index":hi,"nodes":nodes,"leaves":leaves,"empty_nodes":enodes,"empty_leaves":eleaves,"found":found is not None,"full_graph":full_graph}

rows=[]
for k,group in enumerate(core_cases):
 for ci,core in enumerate(group['accepted']):
  for hi in range(27):
   rows.append(solve(core,k,ci,hi))
   if len(rows)%50==0:print('completed',len(rows),flush=True)
assert len(rows)==972
assert all(not r["found"] and r["full_graph"] is None for r in rows)
Path(__file__).with_name('q7_h3_pair_b0_full_exclusion.json').write_text(json.dumps({'scope':'H3 pair profile with independent P: exhaustive completion','cases':rows},indent=2)+'\n')
print('All972 cases exhausted; graphs',sum(r['found'] for r in rows),flush=True)
