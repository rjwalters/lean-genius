from pathlib import Path
import json,hashlib
p=Path(__file__).parent;src=Path('/tmp/erdos85-sol1-q9-elementary-nine-symmetry/results.json'); inp=json.loads(src.read_text()); a=[1,1,1,0,0,0,0,0];b=[1,0,0,1,1,0,0,0];sizes=[3,3]+[9]*8
blocks=[[0,1,3,5],[4,6],[2,7,8,9]];e0=None
for o in inp['orbits']:
 q=[[0,0]+[3*x for x in a],[0,0]+[3*x for x in b]]+[[a[i],b[i]]+r for i,r in enumerate(o['D'])]
 e=[[8*(i==j)+sizes[j]-sum(q[i][k]*q[k][j] for k in range(10)) for j in range(10)] for i in range(10)]
 assert all(sum(r)==5 and min(r)>=0 for r in e)
 if e0 is None:e0=e
 else:assert e==e0
 for h,C in enumerate(blocks):
  for i in C:
   assert all(e[i][j]==0 for j in range(10) if j not in C)
   assert [sum(q[i][j] for j in T) for T in blocks]==[[3,3,3],[4,1,4],[2,2,5]][h]
(p/'results.json').write_text(json.dumps({'status':'PASS','E_quotient':e0,'component_sizes':[sum(sizes[i] for i in C) for C in blocks],'G_component_quotient':[[3,3,3],[4,1,4],[2,2,5]]},indent=2)+'\n')
(p/'input-pin.json').write_text(json.dumps({'path':str(src),'sha256':hashlib.sha256(src.read_bytes()).hexdigest()},indent=2)+'\n');print('PASS: identical deficiency quotients and component partition arithmetic')
