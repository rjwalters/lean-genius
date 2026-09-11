from pathlib import Path
import json,hashlib,time
s=Path('/tmp/erdos85-sol1-q9-order3-f2-symmetry');p=Path(__file__).resolve().parent;start=time.monotonic()
for f,h in json.loads((s/'pins.json').read_text()).items():assert hashlib.sha256((s/f).read_bytes()).hexdigest()==h
pin=json.loads((s/'input-pin.json').read_text());source=Path(pin['path']);assert hashlib.sha256(source.read_bytes()).hexdigest()==pin['sha256']
records={}
for i,r in enumerate(json.loads(source.read_text())):
 for j,T in enumerate(r['tables']):
  key=(r['cross_orbits'],*r['mapping'],*((-1,-1) if r['missing_labels'] is None else r['missing_labels']),*(x for row in T for x in row));assert key not in records;records[key]=(i,j)
assert len(records)==672
swap=(0,2,1)
def transform(w,op):
 k=w[0];pairs=[(i,j) for i,j in enumerate(w[1:4]) if j>=0];missing=w[4:6];entries=[(a,b,w[6+3*a+b]) for a in range(3) for b in range(3)]
 if op==0:
  pairs=[(swap[a],b) for a,b in pairs];entries=[(swap[a],b,x) for a,b,x in entries];missing=(-1,-1) if missing==(-1,-1) else (swap[missing[0]],missing[1])
 elif op==1:
  pairs=[(a,swap[b]) for a,b in pairs];entries=[(a,swap[b],x) for a,b,x in entries];missing=(-1,-1) if missing==(-1,-1) else (missing[0],swap[missing[1]])
 else:pairs=[(b,a) for a,b in pairs];entries=[(b,a,x) for a,b,x in entries];missing=missing[::-1]
 P=[-1]*3;T=[0]*9
 for a,b in pairs:P[a]=b
 for a,b,x in entries:T[3*a+b]=x
 return (k,*P,*missing,*T)
remaining=set(records);out=[]
while remaining:
 assert time.monotonic()-start<60
 root=min(remaining);orbit={root};todo=[root]
 while todo:
  w=todo.pop()
  for op in range(3):
   z=transform(w,op);assert z in records
   if z not in orbit:orbit.add(z);todo.append(z)
 assert orbit<=remaining and len(orbit) in (1,2,4,8);remaining-=orbit;i,j=records[root];out.append({'key':list(root),'size':len(orbit),'state':i,'table':j})
assert out==json.loads((s/'orbits.json').read_text()) and len(out)==117 and sum(r['size'] for r in out)==672
result={'status':'PASS','generator_closure_orbits':117,'covered':672,'size_histogram':{str(k):sum(r['size']==k for r in out) for k in (1,2,4,8)},'seconds':time.monotonic()-start};(p/'results.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
