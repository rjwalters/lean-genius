from pathlib import Path
from fractions import Fraction as F
import json,time,numpy as np
from scipy.optimize import linprog
p=Path(__file__).resolve().parent;start=time.monotonic();data=json.loads((p/'models.json').read_text())['records'];out=[]
for r in data:
 remaining=30-(time.monotonic()-start)
 if remaining<=0:out.append({'root':r['root'],'status':'UNVISITED'});continue
 n=len(r['variables']);ineq=[]
 for ci,c in enumerate(r['constraints']):
  a=[0]*n
  for j,v in c['coefficients']:a[j]=v
  ineq.extend([{'label':['constraint',ci,'upper'],'a':a,'b':c['upper']},{'label':['constraint',ci,'lower'],'a':[-x for x in a],'b':-c['lower']}])
 for j,(l,u) in enumerate(r['bounds']):
  a=[0]*n;a[j]=1
  ineq.extend([{'label':['bound',j,'upper'],'a':a,'b':u},{'label':['bound',j,'lower'],'a':[-x for x in a],'b':-l}])
 A=np.array([c['a'] for c in ineq],float);b=np.array([c['b'] for c in ineq],float)
 sol=linprog(np.zeros(n),A_ub=A,b_ub=b,bounds=[(None,None)]*n,method='highs',options={'time_limit':remaining});result={'root':r['root'],'source_root':r['source_root'],'class':r['class'],'status':'UNKNOWN','solver_status':int(sol.status)}
 if sol.x is not None:
  x=[F(float(v)).limit_denominator(1000000) for v in sol.x]
  if all(sum(v*w for v,w in zip(c['a'],x) if v)<=c['b'] for c in ineq):result.update(status='EXACT_RATIONAL_WITNESS',assignment=[str(v) for v in x])
 elif sol.status==2:
  dual=linprog(b,A_eq=np.vstack([A.T,np.ones(len(ineq))]),b_eq=np.r_[np.zeros(n),1],bounds=(0,None),method='highs',options={'time_limit':max(.01,30-(time.monotonic()-start))})
  if dual.x is not None:
   y=[F(float(v)).limit_denominator(1000000) for v in dual.x];active=[(v,c) for v,c in zip(y,ineq) if v];rhs=sum(v*c['b'] for v,c in active)
   if min(y)>=0 and rhs<0 and all(sum(v*c['a'][j] for v,c in active if c['a'][j])==0 for j in range(n)):result.update(status='EXACT_FARKAS_CONTRADICTION',rhs=str(rhs),terms=[{'label':c['label'],'weight':str(v)} for v,c in zip(y,ineq) if v])
 out.append(result)
r={'status':'COMPLETE' if all(x['status']!='UNKNOWN' and x['status']!='UNVISITED' for x in out) else 'INCOMPLETE','original_cap_seconds':30,'seconds':time.monotonic()-start,'records':out};(p/'results.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({'status':r['status'],'seconds':r['seconds'],'outcomes':{s:sum(x['status']==s for x in out) for s in set(x['status'] for x in out)}}))
