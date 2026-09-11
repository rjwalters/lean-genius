from pathlib import Path
from itertools import product,combinations
import json,hashlib,time
s=Path('/tmp/erdos85-sol1-q9-order3-f2-attached-phases');p=Path(__file__).resolve().parent;start=time.monotonic()
for f,h in json.loads((s/'pins.json').read_text()).items():assert hashlib.sha256((s/f).read_bytes()).hexdigest()==h
orig=json.loads((s/'results.json').read_text());lookup={tuple(r['mapping']):r for r in orig['records']};out=[];total=0
for mapping in product(range(-1,3),repeat=3):
 used=[x for x in mapping if x>=0];k=len(used)
 if k not in (2,3) or len(set(used))!=k:continue
 edges=[(a,3+b) for a,b in enumerate(mapping) if b>=0]+[(4,5),(1,2)]
 good=bad=0
 for shifts in product(range(3),repeat=len(edges)):
  assert time.monotonic()-start<60
  neighbors=[0]*20
  def connect(a,b):neighbors[a]|=1<<b;neighbors[b]|=1<<a
  for label in range(6):
   for t in range(3):connect(label//3,2+3*label+t)
  for (a,b),shift in zip(edges,shifts):
   for t in range(3):connect(2+3*a+t,2+3*b+(t+shift)%3)
  c4=any((neighbors[a]&neighbors[b]).bit_count()>=2 for a,b in combinations(range(20),2))
  # Independently solve vertex potentials on a spanning forest; conflicting cycle sum iff nonzero voltage.
  quotient=[[] for _ in range(6)]
  for (a,b),shift in zip(edges,shifts):quotient[a].append((b,shift));quotient[b].append((a,-shift))
  potential={};nonzero=False
  for root in range(6):
   if root in potential:continue
   potential[root]=0;todo=[root]
   while todo:
    a=todo.pop()
    for b,shift in quotient[a]:
     target=(potential[a]+shift)%3
     if b in potential:nonzero |= potential[b]!=target
     else:potential[b]=target;todo.append(b)
  cyclic={mapping[1],mapping[2]}=={1,2}
  assert c4==(cyclic and not nonzero)
  bad+=c4;good+=not c4;total+=1
 r={'mapping':list(mapping),'valid':good,'c4':bad};expected=lookup[mapping];assert good==expected['valid'] and bad==expected['c4'];out.append(r)
assert len(out)==24 and total==2916 and sum(r['c4'] for r in out)==216
result={'status':'PASS','roots':24,'assignments':total,'c4_free':2700,'c4':216,'per_assignment_voltage_equivalence':True,'seconds':time.monotonic()-start,'original_wall_cap_seconds':60};(p/'results.json').write_text(json.dumps(result,indent=2)+'\n');(p/'root-counts.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(result))
