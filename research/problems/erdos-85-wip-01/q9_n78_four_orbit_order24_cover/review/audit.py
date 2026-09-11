from pathlib import Path
import itertools,json,hashlib
src=Path('/tmp/erdos85-sol1-q9-n78-four-orbit-order24-cover');out=Path(__file__).resolve().parent;pins={}
for mf in ['pins.json','input-pins.json']:
 for n,h in json.loads((src/mf).read_text()).items():
  p=src/n;assert hashlib.sha256(p.read_bytes()).hexdigest()==h;pins[str(p)]=h
for r in json.loads((out/'premise-states.json').read_text()):assert r['status']=='resolved' and r['resolution'].startswith('PASS')
counts={}
for name in ['C8','C4xC2','E8','D8','Q8']:
 def mul(x,y):
  if name=='C8':return (x+y)%8
  if name=='E8':return x^y
  a,b=x//2,x%2;c,d=y//2,y%2
  return 2*((a+(c if name=='C4xC2' or b==0 else -c)+(2*b*d if name=='Q8' else 0))%4)+(b^d)
 kernels=[]
 for rest in itertools.combinations(range(1,8),3):
  K={0,*rest}
  if all(mul(x,y) in K for x in K for y in K):kernels.append(K)
 counts[name]=1+len(kernels)
assert list(counts.values())==[2,4,8,4,4] and sum(counts.values())==22
# Check the nontrivial order3 linear representative splits with a fixed line.
rot=lambda x:((x<<1)&7)|(x>>2)
fixed=[x for x in range(8) if rot(x)==x]
plane=[x for x in range(8) if x^rot(x)^rot(rot(x))==0]
assert len(fixed)==2 and len(plane)==4 and set(fixed)&set(plane)=={0}
assert {x^y for x in fixed for y in plane}==set(range(8))
result={'source_external_pins':len(pins),'accepted_premises':[2278,2298,2314],'characters_including_zero':counts,'normal_C3_models':22,'total_overinclusive_models':24,'fixed_line_size':2,'irreducible_plane_size':4,'scope':'Paper-cover sanity checks only; no group-action or graph search outcome.'}
(out/'input-pins.json').write_text(json.dumps(pins,indent=2)+'\n');(out/'verification.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
