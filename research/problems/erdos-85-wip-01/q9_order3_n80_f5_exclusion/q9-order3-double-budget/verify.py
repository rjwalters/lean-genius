from pathlib import Path
import json
from model import model
p=Path(__file__).resolve().parent;checked=[]
for r in json.loads((p/'results.json').read_text())['records']:
 if r['status']!='EXACT_INFEASIBLE':continue
 m=model(r['code']);coeff=[0]*m['variables'];rhs=0;seen=set()
 for i,v in r['certificate']:
  assert i not in seen and isinstance(v,int) and v>0;seen.add(i);rhs+=v*m['rhs'][i]
  for j,a in m['A'][i].items():coeff[j]+=v*a
 assert min(coeff)>=0 and rhs<0;checked.append({'code':r['code'],'rhs':rhs,'minimum_coefficient':min(coeff)})
(p/'verification.json').write_text(json.dumps({'status':'PASS_EXACT_ARITHMETIC','checked':checked,'independent_model_audit':'pending'},indent=2)+'\n');print(checked)
