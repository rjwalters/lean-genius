from itertools import product
from pathlib import Path
import json,time
p=Path(__file__).parent;start=time.monotonic();out=[];regular=0
# Necessary equitable integer quotient only, not graph or SAT search.
for a in product(range(3),repeat=4):
 for x,y,z in product(range(10),repeat=3):
  # x=01, y=02, z=12; last column forced by the first three row sums.
  u=9-a[0]-x-y;v=9-a[1]-x-z;w=9-a[2]-y-z
  if min(u,v,w)<0 or max(u,v,w)>9 or a[3]+u+v+w!=9:continue
  regular+=1
  q=[[a[0],x,y,u],[x,a[1],z,v],[y,z,a[2],w],[u,v,w,a[3]]]
  square=[[sum(q[i][k]*q[k][j] for k in range(4)) for j in range(4)] for i in range(4)]
  if any(square[i][j]>(28 if i==j else 20) for i in range(4) for j in range(4)):continue
  # Two degree-one internal cyclic orbits both use the antipodal shift10.
  if any(a[i]==a[j]==1 and q[i][j]>0 for i in range(4) for j in range(i)):continue
  out.append(q)
result={'status':'COMPLETE','regular_quotients':regular,'retained':len(out),'seconds':time.monotonic()-start,'quotients':out,'scope':'necessary integer quotient conditions only; no graph exclusion unless retained zero'}
(p/'results.json').write_text(json.dumps(result,indent=2)+'\n');print({k:v for k,v in result.items() if k!='quotients'})
