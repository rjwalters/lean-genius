"""Independent fixed-support products and row-at-a-time empty multicover."""
import itertools,time
stats=dict(singleton_completions=0,cover_nodes=0,full_covers=0,partner_capacity_rejections=0,max_rows=0)
cache={}
def feasible(graph,supports,deadline):
 stats['singleton_completions']+=1
 if time.monotonic()>deadline:raise TimeoutError
 key=tuple(supports)
 if key not in cache:
  types=sorted(set(supports));parts=[]
  def partitions(left,chosen):
   if left==0:parts.append(chosen);return
   first=left&-left
   for mask in types:
    if mask&first and mask&left==mask:partitions(left^mask,chosen+[mask])
  partitions(31,[]);rows=[]
  for partition in parts:
   choices=[[5+i for i,m in enumerate(supports) if m==mask] for mask in partition]
   rows.extend(tuple(sorted(r)) for r in itertools.product(*choices))
  assert len(rows)==len(set(rows));cache[key]=rows
 vertices=range(5,len(graph));demand=tuple(7-len(graph[v]) for v in vertices)
 assert min(demand)>=0 and sum(n*supports[i].bit_count() for i,n in enumerate(demand))==70
 rows=[r for r in cache[key] if all(demand[v-5]>0 for v in r) and all(not(graph[u]&graph[v]) for u,v in itertools.combinations(r,2))]
 stats['max_rows']=max(stats['max_rows'],len(rows));m=len(rows);incidence=[0]*len(demand)
 for i,r in enumerate(rows):
  for v in r:incidence[v-5]|=1<<i
 conflicts=[]
 for r in rows:conflicts.append(sum(1<<j for j,t in enumerate(rows) if len(set(r)&set(t))>=2))
 failed=set()
 def capacity(chosen):
  stats['full_covers']+=1;G=[set(v) for v in graph]+[set() for _ in range(14)]
  for i,row in enumerate(chosen,len(graph)):
   for v in rows[row]:G[i].add(v);G[v].add(i)
  for v in range(len(graph),49):
   possible=0
   for w in range(len(graph),49):
    if v==w:continue
    # Audit hypothetical edge by all common-neighbour pairs, without the search predicate.
    G[v].add(w);G[w].add(v)
    ok=all(len(G[a]&G[b])<=1 for a,b in itertools.combinations(range(49),2))
    G[v].remove(w);G[w].remove(v)
    possible+=ok
   if possible<7-len(G[v]):stats['partner_capacity_rejections']+=1;return False
  return True
 def cover(active,remaining,chosen):
  stats['cover_nodes']+=1
  if time.monotonic()>deadline:raise TimeoutError
  if not any(remaining):return len(chosen)==14 and capacity(chosen)
  if len(chosen)>=14 or active.bit_count()<14-len(chosen):return False
  state=(active,remaining,tuple(sorted(chosen)))
  if state in failed:return False
  for v,n in enumerate(remaining):
   if n and (active&incidence[v]).bit_count()<n:return False
  v=min((v for v,n in enumerate(remaining) if n),key=lambda v:(active&incidence[v]).bit_count());options=active&incidence[v]
  while options:
   bit=options&-options;options-=bit;i=bit.bit_length()-1;r=rows[i]
   if any(remaining[u-5]==0 for u in r):continue
   rem=list(remaining)
   for u in r:rem[u-5]-=1
   avail=active&~conflicts[i]
   for u in r:
    if rem[u-5]==0:avail&=~incidence[u-5]
   if cover(avail,tuple(rem),chosen+[i]):return True
  failed.add(state);return False
 return cover((1<<m)-1,demand,[])
