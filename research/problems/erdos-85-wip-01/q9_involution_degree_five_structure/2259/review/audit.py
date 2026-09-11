from pathlib import Path
from itertools import combinations,product
import hashlib,json
s=Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3/q9-involution-n80-residual-five');p=Path(__file__).parent
for f,h in json.loads((s/'pins.json').read_text()).items():assert hashlib.sha256((s/f).read_bytes()).hexdigest()==h
for f,h in json.loads((s/'input-pins.json').read_text()).items():assert hashlib.sha256(Path(f).read_bytes()).hexdigest()==h
cases=json.loads((s/'cases.json').read_text());assert [c['t'] for c in cases]==[0,1,2];checks=0;totals=[]
for c in cases:
 t=c['t'];ns=[set() for _ in range(10)]
 for a,b in c['edges']:assert a!=b and b not in ns[a];ns[a].add(b);ns[b].add(a)
 tau=c['involution'];assert tau==[i^1 for i in range(10)]
 for i in range(10):assert {tau[j] for j in ns[i]}==ns[tau[i]]
 for a,b in combinations(range(10),2):assert len(ns[a]&ns[b])<=1;checks+=1
 ds=[len(ns[i]) for i in range(0,10,2)];assert ds==c['orbit_degrees'] and len(c['edges'])==9+2*t
 assert sum(len(ns[u]-{0,1}) for u in ns[0])==4+2*t
 candidates=[]
 for b,e,n in product(range(11),repeat=3):
  a=10-b-e-n
  if a>=0 and b+2*e+2*n==6-2*t:
   candidates.append((a,b,e,n));assert 30+2*sum(d*(d-4) for d in ds)+4*n==16-4*t+4*n
 assert sorted(candidates)==sorted(map(tuple,c['attached_count_candidates_n111_n211_n221_n311']))
 assert c['central_attached_k_sum']==8-2*t;totals.append(len(candidates))
assert checks==135 and totals==[10,6,3]
(p/'source-pins.json').write_bytes((s/'pins.json').read_bytes());(p/'results.json').write_text(json.dumps({'status':'PASS','codegrees':checks,'count_candidates':totals},indent=2)+'\n');print('2259 three witnesses and count identities PASS')
