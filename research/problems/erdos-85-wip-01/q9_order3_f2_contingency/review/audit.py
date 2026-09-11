from pathlib import Path
from itertools import product
import json,hashlib,time
s=Path('/tmp/erdos85-sol1-q9-order3-f2-contingency');p=Path(__file__).resolve().parent;start=time.monotonic()
for f,h in json.loads((s/'pins.json').read_text()).items():assert hashlib.sha256((s/f).read_bytes()).hexdigest()==h
E=[[0,0,0],[0,0,1],[0,1,0]]
def mul(A,B):return [[sum(A[a][t]*B[t][b] for t in range(3)) for b in range(3)] for a in range(3)]
def key(k,m,z):return (k,tuple(m),None if z is None else tuple(z))
rs=json.loads((s/'receipts.json').read_text());actual={key(r['cross_orbits'],r['mapping'],r['missing_labels']):r for r in rs};assert len(actual)==len(rs)==78
checked=set();count=0
for mapping in product(range(-1,3),repeat=3):
 vals=[x for x in mapping if x>=0];k=len(vals)
 if k not in (2,3) or len(set(vals))!=k:continue
 P=[[int(mapping[a]==b) for b in range(3)] for a in range(3)];EP=mul(E,P);PE=mul(P,E);C=[[3-EP[a][b]-PE[a][b] for b in range(3)] for a in range(3)]
 for missing in ([None] if k==2 else [None]+list(product(range(3),repeat=2))):
  assert time.monotonic()-start<60
  r=[8-int(a>0)-sum(P[a]) for a in range(3)];t=[8-int(b>0)-sum(P[a][b] for a in range(3)) for b in range(3)]
  if missing is not None:r[missing[0]]-=1;t[missing[1]]-=1
  tables=[]
  for a,b,c,d in product(range(4),repeat=4):
   T=[[a,b,r[0]-a-b],[c,d,r[1]-c-d],[t[0]-a-c,t[1]-b-d,0]];T[2][2]=r[2]-sum(T[2])
   if all(0<=T[i][j]<=C[i][j] for i in range(3) for j in range(3)) and all(sum(T[i][j] for i in range(3))==t[j] for j in range(3)):tables.append(T)
  z=key(k,mapping,missing);checked.add(z);record=actual[z]
  assert r==record['row_margins'] and t==record['column_margins'] and C==record['capacities'] and record['status']=='COMPLETE'
  norm=lambda T:tuple(tuple(row) for row in T)
  assert len(tables)==record['count']==len(record['tables']) and {norm(T) for T in tables}=={norm(T) for T in record['tables']} and tables
  count+=len(tables)
assert checked==set(actual) and count==672
out={'status':'PASS','states':78,'tables':672,'zero_states':0,'seconds':time.monotonic()-start,'original_wall_cap_seconds':60};(p/'results.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
