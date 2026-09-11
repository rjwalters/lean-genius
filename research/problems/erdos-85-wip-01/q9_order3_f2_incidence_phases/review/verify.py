from pathlib import Path
from itertools import combinations
from collections import Counter
import json,hashlib,time
p=Path('/tmp/erdos85-sol1-q9-order3-f2-incidence-phases');out=Path(__file__).parent;start=time.monotonic()
def read(p):return json.loads(p.read_text())
pins=read(p/'pins.json')
for n,h in pins.items():assert hashlib.sha256((p/n).read_bytes()).hexdigest()==h,n
ip=read(p/'input-pin.json');assert hashlib.sha256(Path(ip['path']).read_bytes()).hexdigest()==ip['sha256']
states=read(Path(ip['path']));records=read(p/'partial-graphs.json')
expected={(si,ti) for si,s in enumerate(states) for ti in range(len(s['tables']))};seen=set();degree_hist=Counter();pairs_checked=0
for rec in records:
 key=(rec['state'],rec['table']);assert key in expected-seen;seen.add(key);s=states[key[0]]
 bits=[int(v,16) for v in rec['adjacency_hex']];assert len(bits)==80 and all(0<=v<2**80 for v in bits)
 adj=[{j for j in range(80) if bits[i]&(1<<j)} for i in range(80)]
 assert all(i not in adj[i] and all(i in adj[j] for j in adj[i]) for i in range(80))
 # Independent C4 test: each unordered pair appears in at most one neighborhood.
 owners={}
 for middle,nb in enumerate(adj):
  for pair in combinations(sorted(nb),2):assert pair not in owners,(key,pair,middle,owners.get(pair));owners[pair]=middle
 pairs_checked+=len(owners)
 assert adj[0]==set(range(2,11)) and adj[1]==set(range(11,20))
 assert all(len(adj[i])==9 for i in range(20))
 def tau(i):return i if i<2 else 2+((i-2)//3)*3+(i-2+1)%3
 assert all(tau(tau(tau(i)))==i and ((tau(i)==i)==(i<2)) for i in range(80))
 assert all({tau(j) for j in adj[i]}==adj[tau(i)] for i in range(80))
 for label in range(6):
  expected_labels={2 if label==1 else 1} if label in (1,2) else ({5 if label==4 else 4} if label in (4,5) else set())
  if label<3 and s['mapping'][label]>=0:expected_labels.add(3+s['mapping'][label])
  if label>=3:expected_labels|={a for a,b in enumerate(s['mapping']) if b==label-3}
  for g in range(3):
   actual=[(j-2)//3 for j in adj[2+3*label+g] if 2<=j<20]
   assert len(actual)==len(set(actual)) and set(actual)==expected_labels
 actual_words=[]
 for orbit in range(20):
  word=[]
  for side in range(2):
   neighbours=adj[20+3*orbit]&set(range(2+9*side,11+9*side))
   assert len(neighbours)<=1
   word.append((next(iter(neighbours))-2-9*side)//3 if neighbours else 3)
  actual_words.append(word)
 for i in range(20,80):assert adj[i]<=set(range(2,20)) and len(adj[i])<=2;degree_hist[len(adj[i])]+=1
 assert actual_words==rec['words']
 counts=Counter(map(tuple,actual_words));target=Counter({(a,b):s['tables'][key[1]][a][b] for a in range(3) for b in range(3)})
 if s['cross_orbits']==3:
  if s['missing_labels'] is None:target[3,3]+=1
  else:a,b=s['missing_labels'];target[a,3]+=1;target[3,b]+=1
 assert counts==target
assert seen==expected and len(seen)==672
result={'status':'PASS','pins':len(pins),'all_tables':len(seen),'neighbor_pairs_checked':pairs_checked,'residual_degree_histogram':dict(degree_hist),'seconds':time.monotonic()-start,'solver_calls':0}
(out/'verification.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
(out/'input-pins.json').write_text(json.dumps({str(p/'pins.json'):hashlib.sha256((p/'pins.json').read_bytes()).hexdigest(),ip['path']:ip['sha256']},indent=2)+'\n')
