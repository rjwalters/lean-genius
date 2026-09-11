from pathlib import Path
import json,time
from model import model
p=Path(__file__).resolve().parent;t=time.monotonic();records=[]
for r in map(json.loads,(p/'batch.jsonl').read_text().splitlines()):
 if r['status']!='UNKNOWN_RATIONALIZATION':continue
 m=model(r['code']);y={i:round(v*10**9) for i,v in r['numerical_candidate'] if round(v*10**9)>0};coeff=[0]*m['variables']
 for i,v in y.items():
  for j,a in m['A'][i].items():coeff[j]+=v*a
 bound_x={l[1]:i for i,l in enumerate(m['labels']) if l[0]=='selected_bound'};bound_y={l[2]:i for i,l in enumerate(m['labels']) if l[0]=='edge_bound'}
 def add(i,v):
  y[i]=y.get(i,0)+v
  for j,a in m['A'][i].items():coeff[j]+=v*a
 n=len(m['words'])
 for j in range(n,m['variables']):
  if coeff[j]<0:add(bound_y[j],-coeff[j])
 for j in range(n):
  if coeff[j]<0:add(bound_x[j],-coeff[j])
 rhs=sum(v*m['rhs'][i] for i,v in y.items());ok=min(coeff)>=0 and rhs<0
 records.append({'code':r['code'],'status':'EXACT_REPAIRED_INFEASIBLE' if ok else 'UNRESOLVED','rhs':rhs,'certificate':sorted(y.items()) if ok else None})
(p/'repaired.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in records));summary={'cases':len(records),'exact_repaired':sum(r['status']=='EXACT_REPAIRED_INFEASIBLE' for r in records),'seconds':time.monotonic()-t,'solver_calls':0};(p/'repair-summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary))
