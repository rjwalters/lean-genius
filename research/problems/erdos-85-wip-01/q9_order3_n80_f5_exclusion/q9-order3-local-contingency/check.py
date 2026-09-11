import itertools,json,time,hashlib
from pathlib import Path
root=Path(__file__).resolve().parent
start=time.monotonic(); cap=60
perms=list(itertools.permutations(range(3)))
r=(4,3,3)
rows=[list(itertools.product(range(n+1),repeat=3)) for n in r]
rows=[[x for x in xs if sum(x)==n] for n,xs in zip(r,rows)]
tables=[]
for a,b in itertools.product(rows[0],rows[1]):
 c=tuple(r[j]-a[j]-b[j] for j in range(3))
 if min(c)>=0 and sum(c)==3: tables.append((a,b,c))
records=[]
for direct,*paths in itertools.product(range(6),repeat=4):
 if time.monotonic()-start>cap: raise RuntimeError('UNKNOWN: original 60 second cap reached')
 p=perms[direct]
 bound=[[3 for j in range(3)] for i in range(3)]
 # E P: internally matched source then direct matching.
 for i in (1,2): bound[i][p[3-i]]-=1
 # P E: direct matching then internal edge at receiver.
 for i in range(3):
  if p[i]!=0: bound[i][3-p[i]]-=1
 for z in paths:
  for i,j in enumerate(perms[z]): bound[i][j]-=1
 allowed=[t for t in tables if all(t[i][j]<=bound[i][j] for i in range(3) for j in range(3))]
 cert=None
 if not allowed:
  negative=[(i,j) for i in range(3) for j in range(3) if bound[i][j]<0]
  if negative: cert={'negative_capacity':negative[0]}
  else:
   for mask in range(1,8):
    demand=sum(r[i] for i in range(3) if mask>>i&1)
    capacity=sum(min(r[j],sum(bound[i][j] for i in range(3) if mask>>i&1)) for j in range(3))
    if capacity<demand:
     cert={'rows':mask,'demand':demand,'capacity':capacity};break
  assert cert is not None
 records.append({'direct':direct,'paths':paths,'allowed_tables':len(allowed),'rejection':cert})
result={'status':'COMPLETE','original_wall_cap_seconds':cap,'elapsed_seconds':time.monotonic()-start,'permutations':perms,'table_count':len(tables),'cases':len(records),'rejected':sum(x['allowed_tables']==0 for x in records),'retained':sum(x['allowed_tables']>0 for x in records),'records':records}
(root/'results.json').write_text(json.dumps(result,indent=2)+'\n')
(root/'pins.json').write_text(json.dumps({'files':{name:hashlib.sha256((root/name).read_bytes()).hexdigest() for name in ['check.py','results.json']}},indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ['records','permutations']}))
