from pathlib import Path
from itertools import combinations_with_replacement,product
import hashlib,json,time
s=Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3/q9-involution-n80-ten-cubic-budget');p=Path(__file__).parent;start=time.monotonic()
for f,h in json.loads((s/'pins.json').read_text()).items():assert hashlib.sha256((s/f).read_bytes()).hexdigest()==h
for f,h in json.loads((s/'input-pins.json').read_text()).items():assert hashlib.sha256(Path(f).read_bytes()).hexdigest()==h
checks=0;restricted=set()
for a,b,c in product(range(11),repeat=3):
 n=10-a-b-c
 if n<0:continue
 D=15-b-2*c-2*n;C=b+2*c+3*n
 for ds in combinations_with_replacement(range(6),5):
  if sum(ds)!=D:continue
  internal=45-2*C-sum(d*(d-1) for d in ds)
  direct=70-2*internal-(10+2*D)
  formula=30+2*sum(d*(d-4) for d in ds)+4*n
  assert direct==formula;checks+=1
  if set(ds)<={2,3}:
   assert direct==-2*b-4*c
   if direct>=0:restricted.add((ds.count(3),a,n))
assert restricted=={(1,8,2),(3,9,1),(5,10,0)}
(p/'source-pins.json').write_bytes((s/'pins.json').read_bytes());(p/'results.json').write_text(json.dumps({'status':'PASS','identity_cases':checks,'restricted_cases':sorted(restricted),'seconds':time.monotonic()-start},indent=2)+'\n');print(checks,sorted(restricted))
