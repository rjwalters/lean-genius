from pathlib import Path
from itertools import product
import json,hashlib
p=Path(__file__).parent
survivors=[]
for d in product(range(5),repeat=4):
 a=4+sum(d)
 if a>10:continue
 e=28-2*(10-a)-sum(x*(x-1) for x in d)
 cross=40-2*e-2*a
 assert cross==2*sum(x*(x-4) for x in d)
 if cross>=0 and not (4 in d and 0 in d):survivors.append(d)
assert survivors==[(0,0,0,0)]
sizes=[4,6,8,12,24,24]
Q=[[0,3,0,0,6,0],[2,1,0,2,0,4],[0,0,0,3,3,3],[0,1,2,2,2,2],[1,0,1,1,4,2],[0,1,1,1,2,4]]
assert sum(sizes)==78 and all(sum(row)==9 for row in Q)
assert all(sizes[i]*Q[i][j]==sizes[j]*Q[j][i] for i in range(6) for j in range(6))
Q2=[[sum(Q[i][k]*Q[k][j] for k in range(6)) for j in range(6)] for i in range(6)]
assert Q2[5][3]==13>sizes[3]
result={'status':'PASS_CONDITIONAL_GRAPH_DERIVATION','degree_vectors':625,'survivors':survivors,'sizes':sizes,'Q':Q,'Q_squared':Q2,'contradiction':{'origin_cell':'T_D','endpoint_cell':'S','two_step_walks':13,'endpoint_count':12},'scope':'Paper audit, no Lean or graph solver'}
(p/'results.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
