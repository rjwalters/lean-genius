from pathlib import Path
from itertools import product
import json
p=Path(__file__).resolve().parent
for ds in product(range(5),repeat=4):
 a=4+sum(ds);eR=28-2*(10-a)-sum(d*(d-1) for d in ds)
 assert 40-2*eR-2*a==2*sum(d*(d-4) for d in ds)
 if 2*sum(d*(d-4) for d in ds)>=0:assert all(d in (0,4) for d in ds)
Q=[[0,3,0,0,6,0],[2,1,0,2,0,4],[0,0,0,3,3,3],[0,1,2,2,2,2],[1,0,1,1,4,2],[0,1,1,1,2,4]];sizes=[4,6,8,12,24,24]
assert sum(sizes)==78 and all(sum(r)==9 for r in Q)
assert all(sizes[i]*Q[i][j]==sizes[j]*Q[j][i] for i in range(6) for j in range(6))
square=[[sum(Q[i][k]*Q[k][j] for k in range(6)) for j in range(6)] for i in range(6)]
assert square[5][3]==13>sizes[3]
out={'status':'PASS_ARITHMETIC','degree_vectors_checked':625,'quotient':Q,'sizes':sizes,'quotient_square':square,'contradiction':{'source':'T_K','target':'S','walks':13,'vertices':12},'scope':'arithmetic only; structural proof requires independent review'}
(p/'results.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
