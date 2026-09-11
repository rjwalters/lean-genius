from pathlib import Path
import json,hashlib,itertools,time
p=Path(__file__).parent;src=Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3/q9-involution-n80-t0-deficit-filter');base=src.parent;start=time.monotonic()
pins=json.loads((src/'pins.json').read_text())
for f,h in pins.items():assert hashlib.sha256((src/f).read_bytes()).hexdigest()==h
for f,h in json.loads((src/'input-pins.json').read_text()).items():assert hashlib.sha256(Path(f).read_bytes()).hexdigest()==h
roots=json.loads((base/'q9-involution-n80-t01-incidence/results.json').read_text())['results'];graphs=json.loads((base/'q9-involution-n80-degree-five-centers/representatives.json').read_text());out=[]
for index,case in enumerate(roots[:24]):
 Y=case['witness'];P=set(case['case']['P']);delta=[2-sum(row) for row in Y]
 if any(delta[f]==0 for f in P):continue
 H=[set() for _ in range(10)]
 for a,b in graphs[case['case']['graph_index']]['edges']:H[a].add(b);H[b].add(a)
 owners=sorted(P)+[f for f in range(10) for _ in range(delta[f]-(f in P))];assert len(owners)==6
 central=[1+delta[f]-len(H[f]&P) for f in range(10)];targets=[]
 def rec(path,left,cent):
  n=len(path)
  if n==6:
   if any(left) or any(cent):return
   Z=[[0]*10 for _ in range(10)]
   for a,b in zip(owners,path):Z[a][b]+=1
   if all(Z[a][b]==Z[b][a] for a in range(10) for b in range(10)):targets.append(tuple(path))
   return
  for q in range(10):
   if left[q]==0 or q in H[owners[n]] or (n<4 and cent[q]<=0):continue
   ll=left.copy();cc=cent.copy();ll[q]-=1
   if n<4:cc[q]-=1
   rec(path+[q],ll,cc)
 rec([],delta.copy(),central.copy())
 covered=[sum((not Y[f][j])<<j for j in range(5)) for f in range(10)]
 D=[[sum(Y[g][j] for g in H[f])-(sum(Y[f]) if j==0 else Y[f][0]) for j in range(5)] for f in range(10)]
 tested=survived=0
 for leaves in itertools.permutations(range(1,5)):
  masks=[1|(1<<j) for j in leaves]
  if any(mask&~covered[f] for f,mask in zip(owners[:4],masks)):continue
  choices=[]
  for n in (4,5):
   used=0
   for f,mask in zip(owners[:4],masks):
    if f==owners[n]:used|=mask
   choices.append([mask for mask in range(32) if mask.bit_count()==2 and not(mask&1) and not(mask&~covered[owners[n]]) and not(mask&used)])
  for a,b in itertools.product(*choices):
   if owners[4]==owners[5] and a&b:continue
   allm=masks+[a,b]
   for dest in targets:
    assert time.monotonic()-start<30,'UNKNOWNreview30s'
    tested+=1;T=[[0]*5 for _ in range(10)]
    for q,mask in zip(dest,allm):
     for j in range(5):T[q][j]+=(mask>>j)&1
    survived+=all(T[f][j]>=D[f][j] for f in range(10) for j in range(5))
 assert survived==0
 out.append({'root_index':index,'target_assignments':len(targets),'tested':tested})
expected=json.loads((src/'results.json').read_text())['results'];assert out==[{k:e[k] for k in ('root_index','target_assignments','tested')} for e in expected]
assert len(out)==10 and sum(e['tested'] for e in out)==17640
(p/'results.json').write_text(json.dumps({'source_pins':pins,'independent_results':out,'total':17640,'seconds':time.monotonic()-start,'review_cap_seconds':30,'roots_excluded':0},indent=2)+'\n')
print('PASS ten saved matrices,17640 combinations,zero survivors; no underlyingroot exclusion')
