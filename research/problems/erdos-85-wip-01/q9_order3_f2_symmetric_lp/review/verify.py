from pathlib import Path
import json,hashlib,time,collections
p=Path('/tmp/erdos85-sol1-q9-order3-f2-symmetric-lp');out=Path(__file__).parent
start=time.monotonic()
def read(p):return json.loads(p.read_text())
pins=read(p/'pins.json'); inputs=read(p/'input-pins.json')
for n,h in pins.items():assert hashlib.sha256((p/n).read_bytes()).hexdigest()==h,n
for n,h in inputs.items():assert hashlib.sha256(Path(n).read_bytes()).hexdigest()==h,n
orbits=read(Path('/tmp/erdos85-sol1-q9-order3-f2-symmetry/orbits.json'))
states=read(Path('/tmp/erdos85-sol1-q9-order3-f2-contingency/receipts.json'))
receipts=read(p/'receipts.json');assert len(receipts)==len(orbits)==117
checks=0;denoms=collections.Counter();diagonal_violations=0;nonlinear_violations=0
for k,(o,r) in enumerate(zip(orbits,receipts)):
 assert r['orbit']==k and all(r[t]==o[t] for t in ['state','table','size'])
 assert r['status']=='EXACT_FEASIBLE'; d=r['denominator'];assert type(d)==int and d>0
 denoms[d]+=1
 nums=dict(r['witness']);assert len(nums)==len(r['witness'])
 assert all(type(i)==int and 0<=i<420 and type(v)==int and v>=0 for i,v in nums.items())
 y=[[0]*20 for _ in range(20)];z=[[0]*20 for _ in range(20)];idx=0
 for i in range(20):
  for j in range(i,20):
   y[i][j]=y[j][i]=nums.get(idx,0);z[i][j]=z[j][i]=nums.get(idx+210,0);idx+=1
 s=states[o['state']];T=s['tables'][o['table']]
 words=[]
 for a in range(3):
  for b in range(3):words.extend([(a,b)]*T[a][b])
 if s['cross_orbits']==3:
  if s['missing_labels'] is None:words+=[(3,3)]
  else:words += [(s['missing_labels'][0],3),(3,s['missing_labels'][1])]
 assert len(words)==20
 # Count already occupied attached two-step routes directly by label neighbors.
 attached=[set() for _ in range(6)]
 for i,j in [(1,2),(4,5)]+[(a,3+b) for a,b in enumerate(s['mapping']) if b>=0]:
  attached[i].add(j);attached[j].add(i)
 for i,(a,b) in enumerate(words):
  neighbours=set(([a] if a<3 else [])+([3+b] if b<3 else []))
  assert sum(y[i])==(9-len(neighbours))*d;checks+=1
  assert sum(z[i])<=d;checks+=1
  for label in range(6):
   side,value=divmod(label,3)
   occupied=len(attached[label]&neighbours)
   assert sum(y[i][j] for j,w in enumerate(words) if w[side]==value)<=(3-occupied)*d;checks+=1
  for j in range(20):
   assert 0<=y[i][j]<=2*d and z[i][j]>=max(0,y[i][j]-d);checks+=1
 if any(y[i][i] not in (0,2*d) for i in range(20)):diagonal_violations+=1
 if any(sum(y[i][k]*y[k][j] for k in range(20))+d*d*sum(words[i][h]==words[j][h] and words[i][h]<3 for h in range(2))>3*d*d for i in range(20) for j in range(i+1,20)):nonlinear_violations+=1
result={'status':'PASS','pins_verified':len(pins),'input_pins_verified':len(inputs),'exact_witnesses':len(receipts),'covered_tables':sum(o['size'] for o in orbits),'checks':checks,'denominator_histogram':dict(denoms),'diagnostic_diagonal_invalid_witnesses':diagonal_violations,'diagnostic_nonlinear_invalid_witnesses':nonlinear_violations,'seconds':time.monotonic()-start,'solver_calls':0}
(out/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
(out/'input-pins.json').write_text(json.dumps({str(p/'pins.json'):hashlib.sha256((p/'pins.json').read_bytes()).hexdigest(),**inputs},indent=2)+'\n')
print(json.dumps(result))
