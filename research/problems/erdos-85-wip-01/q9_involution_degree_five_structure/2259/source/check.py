from pathlib import Path
from itertools import combinations,product
import json
p=Path(__file__).parent;cases=[]
for t in range(3):
 edges={(0,1)}|{(0,i) for i in (2,4,6,8)}|{(1,i) for i in (3,5,7,9)}
 for j in range(t):edges.add((2+4*j,4+4*j));edges.add((3+4*j,5+4*j))
 adj=[set() for _ in range(10)]
 for a,b in edges:adj[a].add(b);adj[b].add(a)
 assert all(len(adj[a]&adj[b])<=1 for a,b in combinations(range(10),2))
 assert {tuple(sorted((a^1,b^1))) for a,b in edges}==edges
 d=[len(adj[i]) for i in range(0,10,2)]
 assert sum(d)==len(edges)==9+2*t
 patterns=[]
 for n1,n2,n3 in product(range(11),repeat=3):
  if n1+n2+n3>10 or n1+2*n2+2*n3!=6-2*t:continue
  assert 30+2*sum(x*(x-4) for x in d)+4*n3==16-4*t+4*n3
  patterns.append([10-n1-n2-n3,n1,n2,n3])
 cases.append({'t':t,'edges':sorted(edges),'involution':[i^1 for i in range(10)],'orbit_degrees':d,'attached_count_candidates_n111_n211_n221_n311':patterns,'central_attached_k_sum':8-2*t})
assert len(cases[2]['attached_count_candidates_n111_n211_n221_n311'])==3
assert sorted(cases[2]['attached_count_candidates_n111_n211_n221_n311'])==[[8,2,0,0],[9,0,0,1],[9,0,1,0]]
(p/'cases.json').write_text(json.dumps(cases,indent=2)+'\n');(p/'results.json').write_text(json.dumps({'status':'PASS','residual_shapes':3,'codegree_pairs_checked':135,'counts_per_t':[len(c['attached_count_candidates_n111_n211_n221_n311']) for c in cases],'scope':'Three local residual witnesses and exact count identities; full graph realizability not checked.'},indent=2)+'\n');print('PASS three residual shapes,135 common-neighbor checks,10/6/3 intermediate count profiles')
