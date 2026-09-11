from pathlib import Path
from itertools import combinations,combinations_with_replacement
import json,time
p=Path(__file__).parent;start=time.monotonic();cap=60;profiles=[]
for r in combinations_with_replacement((1,3,5,7),8):
 S=sum(r);R=S
 if sum(x*(x-1) for x in r)>56:continue
 if any((9-x)*x>R for x in r):continue
 profiles.append(r)
assert len(profiles)==11
results=[]
for profile in profiles:
 target=sorted(profile,reverse=True);adj=[set() for _ in range(8)];remaining=target.copy();nodes=[0];solutions=[];status='COMPLETE'
 def dfs(i):
  nodes[0]+=1
  if nodes[0]>1000000 or time.monotonic()-start>cap:raise TimeoutError
  if i==8:
   assert all(len(adj[v])==target[v] for v in range(8));solutions.append([sorted(nb) for nb in adj]);return
  candidates=[j for j in range(i+1,8) if remaining[j]>0];need=remaining[i]
  if need<0 or need>len(candidates):return
  for selected in combinations(candidates,need):
   for j in selected:adj[i].add(j);adj[j].add(i);remaining[j]-=1
   remaining[i]=0
   feasible=all(0<=remaining[j]<=sum(remaining[k]>0 for k in range(i+1,8) if k!=j) for j in range(i+1,8))
   if feasible and all(len(adj[u]&adj[v])<=1 for u,v in combinations(range(8),2)):dfs(i+1)
   remaining[i]=need
   for j in selected:adj[i].remove(j);adj[j].remove(i);remaining[j]+=1
 try:dfs(0)
 except TimeoutError:status='UNKNOWN'
 results.append({'degrees':target,'status':status,'nodes':nodes[0],'solutions':solutions})
result={'status':'COMPLETE' if all(r['status']=='COMPLETE' for r in results) else 'INCOMPLETE','original_wall_cap_seconds':cap,'original_node_cap_per_profile':1000000,'seconds':time.monotonic()-start,'degree_profiles':profiles,'receipts':results,'scope':'Fixed H on eight vertices only; necessary profile filters and complete fixed-degree C4-free enumeration.'}
(p/'results.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k!='receipts'}));print([(r['degrees'],r['status'],r['nodes'],len(r['solutions'])) for r in results])
