from pathlib import Path
import json,time,math
from fractions import Fraction
import numpy as np
from scipy.sparse import coo_matrix
from scipy.optimize import linprog
from model import model
p=Path(__file__).resolve().parent;skip=json.loads((p/'pilot.json').read_text())['code'];cases=[r for r in map(json.loads,(p.parent/'q9-order3-row-supported-color-cover/receipts.jsonl').read_text().splitlines()) if r['status']=='UNKNOWN' and r['code']!=skip];start=time.monotonic();out=(p/'batch.jsonl').open('w');counts={}
for r in cases:
 rec={'code':r['code']}
 if time.monotonic()-start>=60:rec['status']='UNVISITED'
 else:
  m=model(r['code']);n=len(m['A']);triples=[(i,j,v) for i,row in enumerate(m['A']) for j,v in row.items()];A=coo_matrix(([v for i,j,v in triples],([i for i,j,v in triples],[j for i,j,v in triples])),shape=(n,m['variables'])).tocsr()
  s=linprog(np.zeros(n),A_ub=-A.T,b_ub=np.zeros(m['variables']),A_eq=[m['rhs']],b_eq=[-1],bounds=(0,None),method='highs',options={'time_limit':max(.001,60-(time.monotonic()-start))})
  rec.update({'solver_status':int(s.status),'rows':n,'variables':m['variables'],'status':'NO_CERTIFICATE'})
  if s.success:
   rec['numerical_candidate']=[[i,float(x)] for i,x in enumerate(s.x) if x!=0]
   f=[Fraction(float(x)).limit_denominator(1000000) for x in s.x];den=math.lcm(*(x.denominator for x in f));cert=[(i,int(x*den)) for i,x in enumerate(f) if x];coeff=[0]*m['variables']
   for i,v in cert:
    for j,a in m['A'][i].items():coeff[j]+=v*a
   ok=all(v>0 for i,v in cert) and min(coeff)>=0 and sum(v*m['rhs'][i] for i,v in cert)<0
   rec['status']='EXACT_INFEASIBLE' if ok else 'UNKNOWN_RATIONALIZATION'
   if ok:rec['certificate']=cert
 counts[rec['status']]=counts.get(rec['status'],0)+1;out.write(json.dumps(rec)+'\n');out.flush()
out.close();summary={'cases':len(cases),'original_total_wall_cap_seconds':60,'seconds':time.monotonic()-start,'counts':counts,'pilot_excluded_from_batch':skip};(p/'batch-summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary))
