from pathlib import Path
from itertools import combinations,product
import json,time
p=Path(__file__).parent;start=time.monotonic();positions=[(i,j) for i in range(5) for j in range(i,5)];counts={'binary_symmetric':32768,'row_three':0,'no_adjacent_loops':0,'two_step_bound':0};survivors=[]
for bits in product((0,1),repeat=15):
 Q=[[0]*5 for _ in range(5)]
 for b,(i,j) in zip(bits,positions):Q[i][j]=Q[j][i]=b
 if any(sum(r)!=3 for r in Q):continue
 counts['row_three']+=1
 if any(Q[i][i] and Q[j][j] and Q[i][j] for i,j in combinations(range(5),2)):continue
 counts['no_adjacent_loops']+=1
 if any(sum(Q[i][k]*Q[k][j] for k in range(5))>2 for i,j in combinations(range(5),2)):continue
 counts['two_step_bound']+=1;survivors.append(Q)
assert not survivors
(p/'results.json').write_text(json.dumps({'status':'COMPLETE','counts':counts,'seconds':time.monotonic()-start,'scope':'Exact five-orbit quotient arithmetic only; paper proof independent of enumeration.'},indent=2)+'\n');print(counts)
