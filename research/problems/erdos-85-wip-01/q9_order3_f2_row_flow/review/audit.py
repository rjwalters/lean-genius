from pathlib import Path
import json,hashlib,time
p=Path(__file__).resolve().parent;s=Path('/tmp/erdos85-sol1-q9-order3-f2-row-flow');pins=json.loads((s/'pins.json').read_text())
for n,h in pins.items():assert hashlib.sha256((s/n).read_bytes()).hexdigest()==h
link=json.loads((s/'input-pin.json').read_text());raw=Path(link['path']).read_bytes();assert hashlib.sha256(raw).hexdigest()==link['sha256'];inputs=json.loads(raw);rs=json.loads((s/'receipts.json').read_text());expected={(i,j) for i,r in enumerate(inputs) for j in range(len(r['tables']))};seen=set();calls=0;start=time.monotonic()
def cut_flow(n,A,B,need):
 if min(A+B)<0:return -1
 # Min-cut: eliminate the four right-side choices analytically.
 values=[]
 for mask in range(16):
  cap=sum(A[a] for a in range(4) if not(mask>>a&1))
  cap+=sum(min(B[b],sum(n.get((a,b),0) for a in range(4) if mask>>a&1)) for b in range(4))
  values.append(cap)
 return min(need,min(values))
for r in rs:
 assert time.monotonic()-start<60
 key=(r['state'],r['table']);assert key not in seen;seen.add(key);src=inputs[key[0]];T=src['tables'][key[1]];mapping=src['mapping'];n={(a,b):T[a][b] for a in range(3) for b in range(3) if T[a][b]}
 if src['cross_orbits']==3:
  if src['missing_labels'] is None:n[3,3]=1
  else:i,j=src['missing_labels'];n[i,3]=1;n[3,j]=1
 assert sum(n.values())==20 and r['status']=='RETAINED';assert [tuple(t['word']) for t in r['tests']]==sorted(n)
 for test in r['tests']:
  a,b=test['word'];w=(a,b);degree=9-(a<3)-(b<3)
  A=[3-int(a in (1,2) and x==3-a)-int(b<3 and mapping[x]==b) for x in range(3)]+[degree]
  B=[3-int(b in (1,2) and y==3-b)-int(a<3 and mapping[a]==y) for y in range(3)]+[degree]
  success=False
  for trial in test['trials']:
   left=n.copy();left[w]-=1;aa=A.copy();bb=B.copy()
   if trial['double'] is None:need=degree
   else:
    v=tuple(trial['double']);assert v in n;selfloop=trial['selfloop'];assert not selfloop or v==w
    if not selfloop:left[v]-=1
    assert min(left.values())>=0
    if v[0]<3 and v[1]<3:left[v]=0
    aa[v[0]]-=2;bb[v[1]]-=2;need=degree-2
   val=cut_flow(left,aa,bb,need);assert val==trial['flow'] and need==trial['need'];success|=val==need;calls+=1
  assert success and test['supported']
assert seen==expected and len(seen)==672 and calls==6838
out={'status':'PASS','tables':672,'flow_values_verified':calls,'method':'16 exact left-side min-cut formulas per flow, no augmenting paths','seconds':time.monotonic()-start,'original_audit_wall_cap_seconds':60,'source_pins':pins};(p/'results.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
