from pathlib import Path
import json,itertools,hashlib
p=Path(__file__).parent;source=p.parent/'q9-n78-m13-quotient';pins=json.loads((source/'pins.json').read_text())
for f,h in pins.items():assert hashlib.sha256((source/f).read_bytes()).hexdigest()==h
v=json.loads((source/'verification.json').read_text())

a,b=v['representatives'];assert len(v['representatives'])==2
for q in [a,b]:assert all(sum(q[i][k]*q[k][j] for k in range(6))==(21 if i==j else 12) for i in range(6) for j in range(6))
assert all(a[i][i]==0 and sorted(a[i][j] for j in range(6) if j!=i)==[1,1,1,3,3] for i in range(6))
triangles=[ss for ss in itertools.combinations(range(6),3) if all(a[i][j]==3 for i,j in itertools.combinations(ss,2))]
assert len(triangles)==2 and set(triangles[0]).isdisjoint(triangles[1])
zero=[(i,j) for i in range(6) for j in range(i+1,6) if b[i][j]==0]
assert len(zero)==6 and all(sum(i in e for e in zero)==2 for i in range(6))
assert not any(all(tuple(sorted(e)) in zero for e in itertools.combinations(ss,2)) for ss in itertools.combinations(range(6),3))
matchings=[es for es in itertools.combinations(zero,3) if len({i for e in es for i in e})==6];assert len(matchings)==2
r={'status':'PASS','type_a_degree3_triangles':triangles,'type_b_zero_edges':zero,'type_b_shift_pairings':matchings,'scope':'Finite quotient shape checks only; paper implications in PROOF.md'}
(p/'results.json').write_text(json.dumps(r,indent=2)+'\n');(p/'source-pins.json').write_text(json.dumps(pins,indent=2)+'\n');print(r)
