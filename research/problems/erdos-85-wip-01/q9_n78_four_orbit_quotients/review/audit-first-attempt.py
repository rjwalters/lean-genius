from pathlib import Path
import itertools,json,hashlib,time
start=time.monotonic();out=Path(__file__).resolve().parent;src=Path('/tmp/erdos85-sol1-q9-n78-four-orbit-quotients');pins={}
for mf in ['pins.json','input-pins.json']:
 for n,h in json.loads((src/mf).read_text()).items():
  p=src/n;assert hashlib.sha256(p.read_bytes()).hexdigest()==h;pins[str(p)]=h
  if mf=='input-pins.json':
   for a,b in json.loads(p.read_text()).items():
    q=p.parent/a;assert hashlib.sha256(q.read_bytes()).hexdigest()==b;pins[str(q)]=b
for r in json.loads((out/'premise-states.json').read_text()):assert r['status']=='resolved' and r['resolution'].startswith('PASS')
saved=json.loads((src/'results.json').read_text());assert saved['status']=='COMPLETE'
expected={(r['automorphism_order'],tuple(r['sizes'])):r for r in saved['partitions']}
partitions=set()
for order in [d for d in range(1,49) if 48%d==0]:
 div=[d for d in range(1,order+1) if order%d==0]
 for a,b,c in itertools.product(div,repeat=3):
  d=78-a-b-c
  if a<=b<=c<=d and d in div:partitions.add((order,(a,b,c,d)))
assert partitions==set(expected)
records=[]
for order,n in sorted(partitions):
 Q=[[0]*4 for _ in range(4)];found=set();count=[0]
 def rows(i):
  if time.monotonic()-start>30:raise TimeoutError('Original independent30s audit cap exceeded')
  if i==4:
   count[0]+=1
   # Weighted Q squared gives the number of ordered distinct endpoint pairs.
   for a in range(4):
    for b in range(a,4):
     pairs=sum(n[k]*Q[k][a]*(Q[k][b]-(1 if a==b else 0)) for k in range(4))
     capacity=n[a]*(n[b]-(1 if a==b else 0))
     if pairs>capacity:return
   found.add(tuple(tuple(row) for row in Q));return
  remainder=9-sum(Q[i][:i])
  if remainder<0:return
  def entries(j,left):
   if j==4:
    if left==0:rows(i+1)
    return
   for v in range(left+1):
    if j==i:
     if v>=n[i]:continue
     Q[i][i]=v;entries(j+1,left-v)
    else:
     if n[i]*v%n[j]:continue
     reverse=n[i]*v//n[j]
     if reverse>9 or v>n[j]:continue
     Q[i][j]=v;Q[j][i]=reverse;entries(j+1,left-v)
  entries(i,remainder)
 rows(0)
 r=expected[(order,n)];assert found=={tuple(map(tuple,q)) for q in r['quotients']};assert count[0]==r['degree_pass']
 records.append({'order':order,'sizes':n,'degree_matrices':count[0],'survivors':len(found)})
 if n==(6,24,24,24):
  canonical=set()
  for q in found:
   residual=next(j for j in range(1,4) if q[0][j]==0);others=[j for j in range(1,4) if j!=residual];perm=[0,*others,residual]
   canonical.add(tuple(tuple(q[i][j] for j in perm) for i in perm))
  assert canonical=={((1,4,4,0),(1,a,5-a,3),(1,5-a,a,3),(0,3,3,3)) for a in (1,4)}
 if n==(6,8,16,48):assert len(found)==1 and next(iter(found))[1][1]==3
result={'status':'COMPLETE','original_audit_cap_seconds':30,'seconds':time.monotonic()-start,'partitions':records,'canonical_parameters':[1,4],'scope':'Complete necessary degree-quotient cover; cubic8 exclusion and matching consequences separately audited on paper.'}
assert result['seconds']<30
(out/'input-pins.json').write_text(json.dumps(pins,indent=2)+'\n');(out/'verification.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
