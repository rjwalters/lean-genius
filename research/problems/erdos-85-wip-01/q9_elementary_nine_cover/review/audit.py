from pathlib import Path
import json,hashlib,time
s=Path('/tmp/erdos85-sol1-q9-elementary-nine-cover');p=Path(__file__).resolve().parent
for f,h in json.loads((s/'pins.json').read_text()).items():assert hashlib.sha256((s/f).read_bytes()).hexdigest()==h
A={0,1,2};B={0,3,4};a=[int(i in A) for i in range(8)];b=[int(i in B) for i in range(8)];start=time.monotonic();rows=[]
# Generate fixed-sum bounded compositions, rather than producer Cartesian row product.
for j in range(8):
 domain=[]
 def compose(prefix,total,norm):
  k=len(prefix)
  if k==8:
   if total==0:domain.append(tuple(prefix))
   return
  for x in ((0,2) if k==j else range(4)):
   if x<=total and norm+x*x<=17-3*(a[j]+b[j]):compose(prefix+[x],total-x,norm+x*x)
 compose([],9-a[j]-b[j],0);rows.append(domain)
roots=[];saved=[];stopped_global=False
for u,v in [(u,v) for u in sorted(A) for v in sorted(B) if (u==0)==(v==0)]:
 domains=[]
 for j in range(8):
  ca=2+int(j!=u) if j in A else 3;cb=2+int(j!=v) if j in B else 3
  domains.append([r for r in rows[j] if sum(r[i] for i in A)==ca and sum(r[i] for i in B)==cb])
 nodes=0;limited=False;found=[]
 def dfs(chosen,remaining):
  global nodes,limited,stopped_global
  if nodes>=100000 or time.monotonic()-start>=60:limited=True;stopped_global=True;return
  nodes+=1
  if not remaining:
   found.append([chosen[i] for i in range(8)]);return
  # Independent dynamic minimum-compatible-domain ordering, with forward checking.
  viable={}
  for j in remaining:
   viable[j]=[r for r in domains[j] if all(r[i]==t[j] and sum(r[k]*t[k] for k in range(8))+3*a[i]*a[j]+3*b[i]*b[j]<=9 for i,t in chosen.items())]
   if not viable[j]:return
  j=min(remaining,key=lambda j:(len(viable[j]),-j))
  for r in reversed(viable[j]):
   chosen[j]=r;dfs(chosen,remaining-{j});del chosen[j]
   if limited:return
 if not stopped_global:dfs({},set(range(8)))
 status='UNKNOWN' if limited else 'UNVISITED' if stopped_global else 'COMPLETE'
 roots.append({'isolated_A':u,'isolated_B':v,'status':status,'nodes':nodes,'retained':len(found),'domain_sizes':list(map(len,domains))})
 saved.extend({'isolated_A':u,'isolated_B':v,'D':D} for D in found)
(p/'matrices.json').write_text(json.dumps(saved)+'\n');result={'roots':roots,'seconds':time.monotonic()-start,'original_node_cap_per_root':100000,'original_aggregate_wall_cap':60};(p/'results.json').write_text(json.dumps(result,indent=2)+'\n')
assert all(r['status']=='COMPLETE' for r in roots)
orig=json.loads((s/'matrices.json').read_text())
def key(r):return (r['isolated_A'],r['isolated_B'],tuple(tuple(x) for x in r['D']))
assert len(saved)==len(orig)==16 and {key(r) for r in saved}=={key(r) for r in orig}
for x,y in zip(roots,json.loads((s/'results.json').read_text())['roots']):assert x['domain_sizes']==y['domain_sizes'] and x['retained']==y['retained']
print(json.dumps(result))
