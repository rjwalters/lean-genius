from pathlib import Path
import itertools,json,time,hashlib
out=Path(__file__).parent; start=time.monotonic(); cap=60; nodecap=100000
A=(0,1,2);B=(0,3,4);a=[int(i in A) for i in range(8)];b=[int(i in B) for i in range(8)]
roots=[(u,v) for u in A for v in B if (u==0)==(v==0)]
base=[]
for j in range(8):
 rows=[]
 for r in itertools.product(*[(0,2) if i==j else range(4) for i in range(8)]):
  if sum(r)==9-a[j]-b[j] and sum(x*x for x in r)<=17-3*(a[j]+b[j]):rows.append(r)
 base.append(rows)
order=[0,1,3,2,4,5,6,7];receipts=[];saved=[]
for u,v in roots:
 domains=[]
 for j in range(8):
  ca=3 if not a[j] else 2+int(j!=u);cb=3 if not b[j] else 2+int(j!=v)
  domains.append([r for r in base[j] if sum(r[i] for i in A)==ca and sum(r[i] for i in B)==cb])
 nodes=0;leaves=0;stopped=False;selected={}
 def dfs(depth):
  global nodes,leaves,stopped
  if nodes>=nodecap or time.monotonic()-start>=cap:stopped=True;return
  nodes+=1
  if depth==8:
   leaves+=1
   if len(saved)<24:saved.append({'isolated_A':u,'isolated_B':v,'D':[selected[i] for i in range(8)]})
   return
  j=order[depth]
  for r in domains[j]:
   if any(r[i]!=s[j] for i,s in selected.items()):continue
   if any(sum(x*y for x,y in zip(r,s))+3*a[i]*a[j]+3*b[i]*b[j]>9 for i,s in selected.items()):continue
   selected[j]=r;dfs(depth+1);del selected[j]
   if stopped:return
 dfs(0)
 receipts.append({'isolated_A':u,'isolated_B':v,'status':'UNKNOWN' if stopped else 'COMPLETE','nodes':nodes,'retained':leaves,'domain_sizes':list(map(len,domains))})
result={'original_node_cap_per_root':nodecap,'original_aggregate_wall_cap':cap,'seconds':time.monotonic()-start,'roots':receipts,'saved_matrices':len(saved),'scope':'necessary quotient only; no phases or graph witness'}
(out/'results.json').write_text(json.dumps(result,indent=2)+'\n');(out/'matrices.json').write_text(json.dumps(saved)+'\n');print(json.dumps(result))
