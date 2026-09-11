from pathlib import Path
import json,time,math
from fractions import Fraction
import numpy as np
from scipy.sparse import coo_matrix
from scipy.optimize import linprog
from model import model
p=Path(__file__).resolve().parent
r=next(r for r in map(json.loads,(p.parent/'q9-order3-row-supported-color-cover/receipts.jsonl').read_text().splitlines()) if r['status']=='UNKNOWN');m=model(r['code']);n=len(m['A']);triples=[(i,j,v) for i,row in enumerate(m['A']) for j,v in row.items()];A=coo_matrix(([v for i,j,v in triples],([i for i,j,v in triples],[j for i,j,v in triples])),shape=(n,m['variables'])).tocsr();t=time.monotonic();s=linprog(np.zeros(n),A_ub=-A.T,b_ub=np.zeros(m['variables']),A_eq=[m['rhs']],b_eq=[-1],bounds=(0,None),method='highs',options={'time_limit':60});out={'code':m['code'],'original_wall_cap_seconds':60,'seconds':time.monotonic()-t,'rows':n,'variables':m['variables'],'words':len(m['words']),'edges':len(m['edges']),'solver_status':int(s.status),'status':'NO_EXACT_CERTIFICATE'}
if s.success:
 f=[Fraction(float(x)).limit_denominator(1000000) for x in s.x];den=math.lcm(*(x.denominator for x in f));cert=[(i,int(x*den)) for i,x in enumerate(f) if x];coeff=[0]*m['variables']
 for i,v in cert:
  for j,a in m['A'][i].items():coeff[j]+=v*a
 assert all(v>0 for i,v in cert) and min(coeff)>=0 and sum(v*m['rhs'][i] for i,v in cert)<0
 out['status']='EXACT_INFEASIBLE';out['certificate']=cert
(p/'pilot.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
