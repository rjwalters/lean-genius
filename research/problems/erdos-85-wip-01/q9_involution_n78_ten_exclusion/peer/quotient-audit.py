from pathlib import Path
import json
sizes=[4,6,8,12,24,24]
q=[[0,3,0,0,6,0],[2,1,0,2,0,4],[0,0,0,3,3,3],[0,1,2,2,2,2],[1,0,1,1,4,2],[0,1,1,1,2,4]]
assert sum(sizes)==78 and all(sum(r)==9 for r in q)
assert all(sizes[i]*q[i][j]==sizes[j]*q[j][i] for i in range(6) for j in range(6))
square=[[sum(q[i][k]*q[k][j] for k in range(6)) for j in range(6)] for i in range(6)]
violations=[{'source':i,'target':j,'two_step_walks':square[i][j],'endpoint_count':sizes[j]} for i in range(6) for j in range(6) if i!=j and square[i][j]>sizes[j]]
assert square[5][3]==13 and sizes[3]==12
result={'status':'CONDITIONAL_ARITHMETIC_PASS','scope':'does not verify graph derivation of equitable cells','sizes':sizes,'Q':q,'Q_squared':square,'violations':violations}
(Path(__file__).parent/'results.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(violations))
