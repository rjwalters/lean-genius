from pathlib import Path
import json,time
import numpy as np
from scipy.sparse import coo_matrix
from scipy.optimize import linprog
from model import model
p=Path(__file__).resolve().parent;start=time.monotonic();records=[]
for code in [669268,24538199]:
 m=model(code);triples=[(i,j,v) for i,row in enumerate(m['A']) for j,v in row.items()];n=len(m['A']);A=coo_matrix(([v for i,j,v in triples],([i for i,j,v in triples],[j for i,j,v in triples])),shape=(n,m['variables'])).tocsr();r={'code':code,'rows':n,'variables':m['variables']}
 if time.monotonic()-start>=60:r['status']='UNVISITED';records.append(r);continue
 s=linprog(np.zeros(n),A_ub=-A.T,b_ub=np.zeros(m['variables']),A_eq=[m['rhs']],b_eq=[-1],bounds=(0,None),method='highs',options={'time_limit':max(.001,60-(time.monotonic()-start))});r['solver_status']=int(s.status);r['status']='NO_CERTIFICATE'
 if s.success:
  r['numerical_candidate']=[[i,float(v)] for i,v in enumerate(s.x) if v!=0];(p/f'candidate-{code}.json').write_text(json.dumps(r)+'\n')
  y={i:round(v*10**9) for i,v in r['numerical_candidate'] if round(v*10**9)>0};coeff=[0]*m['variables']
  for i,v in y.items():
   for j,a in m['A'][i].items():coeff[j]+=v*a
  bounds={}
  for i,l in enumerate(m['labels']):
   if l[0]=='selected_bound':bounds[l[1]]=i
   if l[0] in ('edge_bound','excess_upper'):bounds[l[2]]=i
  for j in range(m['variables']-1,-1,-1):
   if coeff[j]<0:
    i=bounds[j];v=-coeff[j];y[i]=y.get(i,0)+v
    for k,a in m['A'][i].items():coeff[k]+=v*a
  rhs=sum(v*m['rhs'][i] for i,v in y.items());ok=min(coeff)>=0 and rhs<0;r['status']='EXACT_INFEASIBLE' if ok else 'UNKNOWN_REPAIR';r['rhs']=rhs
  if ok:r['certificate']=sorted(y.items())
 r.pop('numerical_candidate',None);records.append(r)
(p/'results.json').write_text(json.dumps({'original_total_wall_cap_seconds':60,'seconds':time.monotonic()-start,'records':records},indent=2)+'\n');print([{k:v for k,v in r.items() if k!='certificate'} for r in records])
