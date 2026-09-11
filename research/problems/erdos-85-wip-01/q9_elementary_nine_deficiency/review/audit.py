from pathlib import Path
import json,hashlib,itertools
p=Path(__file__).resolve().parent;s=Path('/tmp/erdos85-sol1-q9-elementary-nine-deficiency');pins=json.loads((s/'pins.json').read_text())
for n,h in pins.items():assert hashlib.sha256((s/n).read_bytes()).hexdigest()==h
link=json.loads((s/'input-pin.json').read_text());raw=Path(link['path']).read_bytes();assert hashlib.sha256(raw).hexdigest()==link['sha256'];reps=json.loads(raw)['orbits'];expected=json.loads((s/'results.json').read_text());sizes=[3,3]+[9]*8;blocks=[[0,1,3,5],[4,6],[2,7,8,9]]
for rep in reps:
 Q=[[0]*10 for _ in range(10)]
 for i in range(8):
  for j in range(8):Q[i+2][j+2]=rep['D'][i][j]
 for center,indices in [(0,[0,1,2]),(1,[0,3,4])]:
  for i in indices:Q[center][i+2]=3;Q[i+2][center]=1
 E=[[8*int(i==j)+sizes[j]-sum(Q[i][k]*Q[k][j] for k in range(10)) for j in range(10)] for i in range(10)]
 assert E==expected['E_quotient'];assert all(sum(row)==5 for row in E)
 R=[]
 for group in blocks:
  rows=[tuple(sum(Q[i][j] for j in target) for target in blocks) for i in group];assert len(set(rows))==1;R.append(list(rows[0]))
 assert R==expected['G_component_quotient']
 assert [sum(sizes[i] for i in b) for b in blocks]==[24,18,36]
 assert [[sum(R[i][k]*R[k][j] for k in range(3)) for j in range(3)] for i in range(3)]==[[3*int(i==j)+[24,18,36][j] for j in range(3)] for i in range(3)]
V=list(itertools.product(range(3),repeat=2));nonzero=V[1:];count=0
for S in itertools.combinations(nonzero,4):
 if set(S)!={tuple(-x%3 for x in a) for a in S}:continue
 seen={(0,0)};todo=[(0,0)]
 for v in todo:
  for a in S:
   w=tuple((v[i]+a[i])%3 for i in range(2))
   if w not in seen:seen.add(w);todo.append(w)
 assert len(seen)==9;count+=1
assert count==6
(p/'results.json').write_text(json.dumps({'status':'PASS','representatives_checked':2,'connected_degree4_cayley_sets':count,'source_pins':pins},indent=2)+'\n');print('PASS: both quotient calculations and all six inverse-closed degree4 Cayley graphs.')
