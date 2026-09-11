from pathlib import Path
from itertools import product,combinations
import json,hashlib,time
start=time.monotonic(); src=Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3/q9-involution-n80-eight-fixed');dst=Path(__file__).parent
pins=json.loads((src/'pins.json').read_text())
for p,h in pins.items():assert hashlib.sha256((src/p).read_bytes()).hexdigest()==h
for p,h in json.loads((src/'input-pins.json').read_text()).items():assert hashlib.sha256(Path(p).read_bytes()).hexdigest()==h
saved=json.loads((src/'results.json').read_text()); profiles=[];count=0
for a,b,c in product(range(9),repeat=3):
 d=8-a-b-c
 if d<0:continue
 count+=1;rr=[1]*a+[3]*b+[5]*c+[7]*d;S=sum(rr)
 if sum(x*(x-1) for x in rr)<=56 and all(x*(9-x)<=S for x in rr):profiles.append(rr)
assert count==165 and sorted(profiles)==sorted(saved['degree_profiles'])
positive=0
for receipt in saved['receipts']:
 assert receipt['status']=='COMPLETE'
 seen=set()
 for graph in receipt['solutions']:
  ns=list(map(set,graph));assert list(map(len,ns))==receipt['degrees']
  assert all(i not in ns[i] and all(i in ns[j] for j in ns[i]) for i in range(8))
  assert all(len(ns[i]&ns[j])<=1 for i,j in combinations(range(8),2))
  key=tuple(tuple(sorted(n)) for n in ns);assert key not in seen;seen.add(key);positive+=1
 expected=105 if receipt['degrees']==[1]*8 else (1 if sorted(receipt['degrees'])==[1]*7+[7] else 0)
 assert len(seen)==expected
assert positive==106
result={'status':'PASS','count_vectors':count,'profiles':len(profiles),'positive_fixed_graphs_verified':positive,'negative_completeness':'paper argument audited; DFS not replayed','seconds':time.monotonic()-start}
(dst/'results.json').write_text(json.dumps(result,indent=2)+'\n');(dst/'source-pins.json').write_bytes((src/'pins.json').read_bytes());print(result)
