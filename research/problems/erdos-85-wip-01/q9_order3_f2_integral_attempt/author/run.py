from pathlib import Path
import json,time,hashlib,importlib.util,os
import numpy as np
import scipy
from scipy.optimize import milp,Bounds,LinearConstraint
from scipy.sparse import coo_matrix
p=Path(__file__).parent;src=Path('/tmp/erdos85-sol1-q9-order3-f2-model-generator')
spec=importlib.util.spec_from_file_location('generator',src/'generate.py');g=importlib.util.module_from_spec(spec);spec.loader.exec_module(g)
manifest=json.loads((src/'model-manifest.json').read_text())
started=time.monotonic();receipts=[]
def save():
 (p/'receipts.json').write_text(json.dumps({'original_aggregate_seconds':180,'original_per_root_seconds':2,'original_node_limit':1000,'elapsed_seconds':time.monotonic()-started,'scipy':scipy.__version__,'roots':receipts},indent=2)+'\n')
for index in range(117):
 remaining=180-(time.monotonic()-started)
 if remaining<=0:
  receipts.append({'root':index,'status':'UNVISITED'});continue
 m=g.build(index);raw=g.data(m);assert hashlib.sha256(raw).hexdigest()==manifest[index]['sha256']
 n=m['variables']['count'];rows=m['constraints'];rr=[];cc=[];vv=[]
 for i,row in enumerate(rows):
  for j,v in row['terms']:rr.append(i);cc.append(j);vv.append(v)
 A=coo_matrix((vv,(rr,cc)),shape=(len(rows),n)).tocsc()
 lo=np.array([-np.inf if r['lower'] is None else r['lower'] for r in rows]);hi=np.array([np.inf if r['upper'] is None else r['upper'] for r in rows])
 upper=np.full(n,np.inf);upper[:420]=1;integer=np.zeros(n);integer[:420]=1
 remaining=180-(time.monotonic()-started)
 if remaining<=0:receipts.append({'root':index,'status':'UNVISITED'});continue
 cap=min(2,remaining);begin=time.monotonic()
 result=milp(np.zeros(n),integrality=integer,bounds=Bounds(np.zeros(n),upper),constraints=LinearConstraint(A,lo,hi),options={'time_limit':cap,'node_limit':1000,'mip_rel_gap':0.0})
 # Persist the complete returned vector before interpreting or rounding it.
 returned={'root':index,'solver_status':int(result.status),'message':result.message,'x':None if result.x is None else result.x.tolist(),'mip_node_count':None if getattr(result,'mip_node_count',None) is None else int(result.mip_node_count)}
 (p/f'numerical-{index}.json').write_text(json.dumps(returned,separators=(',',':'))+'\n')
 receipt={'root':index,'solver_status':int(result.status),'seconds':time.monotonic()-begin,'allocated_seconds':cap,'status':'UNKNOWN'}
 if result.x is not None:
  binary=[int(round(x)) for x in result.x[:420]]
  Q=[[0]*20 for _ in range(20)]
  for k,(i,j) in enumerate(m['matrix_pair_order']):Q[i][j]=Q[j][i]=binary[k]+binary[210+k]
  valid=all(x in (0,1) for x in binary) and all(binary[210+k]<=binary[k] for k in range(210))
  valid=valid and all(Q[i][i] in (0,2) and sum(v==2 for v in Q[i])<=1 for i in range(20))
  # All non-product model rows involve binary variables only; evaluate exactly.
  for row in rows:
   if row['name'][0] in ('product_lower','two_step'):continue
   value=sum(binary[j]*c for j,c in row['terms'])
   valid=valid and (row['lower'] is None or value>=row['lower']) and (row['upper'] is None or value<=row['upper'])
  for i in range(20):
   for j in range(i):
    h=sum(m['words'][i][s]<3 and m['words'][i][s]==m['words'][j][s] for s in range(2))
    valid=valid and sum(Q[i][k]*Q[k][j] for k in range(20))+h<=3
  if valid:
   (p/f'witness-{index}.json').write_text(json.dumps({'root':index,'Q':Q},indent=2)+'\n');receipt['status']='EXACT_QUOTIENT_WITNESS'
  else:receipt['candidate_failed_exact_check']=True
 elif result.status==2:receipt['status']='UNVERIFIED_INFEASIBLE'
 receipts.append(receipt);save();print(index,receipt['status'],round(receipt['seconds'],3),flush=True)
save();print('TERMINAL',dict((s,sum(r['status']==s for r in receipts)) for s in sorted({r['status'] for r in receipts})),flush=True)
