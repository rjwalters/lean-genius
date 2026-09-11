from pathlib import Path
import json,hashlib,importlib.util
from base import independent
s=Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3/q9-order3-double-budget');d=Path(__file__).resolve().parent
for f,h in json.loads((s/'pins.json').read_text()).items():assert hashlib.sha256((s/f).read_bytes()).hexdigest()==h
pin=json.loads((s/'dependency.json').read_text());assert hashlib.sha256(Path(pin['path']).read_bytes()).hexdigest()==pin['sha256']
spec=importlib.util.spec_from_file_location('double_producer',s/'model.py');mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
rs=json.loads((s/'results.json').read_text())['records'];assert len(rs)==2 and {r['code'] for r in rs}=={669268,24538199}
checks=[]
for r in rs:
 m=independent(r['code']);base=m['variables'];n=len(m['words'])
 for i in range(n):
  extras=[]
  for k,(u,v) in enumerate(m['edges']):
   if i not in (u,v):continue
   y=n+k;t=m['variables'];m['variables']+=1;extras.append(t)
   m['A'].append({y:1,i:-1,t:-1});m['rhs'].append(0);m['labels'].append(['excess_lower',i,y,t])
   m['A'].append({t:1,i:-1});m['rhs'].append(0);m['labels'].append(['excess_upper',i,t])
  row={t:1 for t in extras};row[i]=-1;m['A'].append(row);m['rhs'].append(0);m['labels'].append(['double_budget',i])
 for i in range(n):
  for j in range(i+1,n):
   if sum(a==b for a,b in zip(m['words'][i],m['words'][j]))>3:
    m['A'].append({i:1,j:1});m['rhs'].append(1);m['labels'].append(['word_incompatible',i,j])
 m['base_variables']=base;assert m==mod.model(r['code'])
 if r['status']!='EXACT_INFEASIBLE':
  assert r['code']==24538199;continue
 assert r['code']==669268
 coeff=[0]*m['variables'];right=0;seen=set()
 for i,v in r['certificate']:
  assert isinstance(i,int) and 0<=i<len(m['A']) and i not in seen and isinstance(v,int) and v>0;seen.add(i)
  right+=v*m['rhs'][i]
  for j,a in m['A'][i].items():coeff[j]+=v*a
 assert min(coeff)>=0 and right==-999999723
 checks.append({'code':r['code'],'variables':m['variables'],'rows':len(m['A']),'certificate_terms':len(seen),'rhs':right,'minimum_coefficient':min(coeff)})
assert len(checks)==1
out={'status':'PASS','independent_models':2,'exact_certificates':checks,'unresolved_preserved':24538199,'solver_calls':0};(d/'results.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
