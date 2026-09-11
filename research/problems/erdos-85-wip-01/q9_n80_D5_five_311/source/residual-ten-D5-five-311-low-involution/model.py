from pathlib import Path
import json,time
p=Path(__file__).resolve().parent;b=p.parent;start=time.monotonic();old=json.loads((b/'residual-ten-D5-five-311-common-neighbor-cuts/models.json').read_text())['records'];results={r['root']:r for r in json.loads((b/'residual-ten-D5-five-311-common-neighbor-cuts/results.json').read_text())['records']};prop={r['root']:r for r in json.loads((b/'residual-ten-D5-five-311-low-propagation/results.json').read_text())['records']};edgecases={r['root']:r for r in json.loads((b/'residual-ten-D5-five-311-low-edge-capacity/results.json').read_text())['records']};out=[]
for m in old:
 if results[m['root']]['status']=='EXACT_FARKAS_CONTRADICTION':continue
 assert time.monotonic()-start<30
 src=m['source_root'];ai=m['assignment'];lows=next(a['lows'] for a in edgecases[src]['survivors'] if a['assignment']==ai);a=next(a for a in prop[src]['survivors'] if a['assignment']==ai);active={tuple(x):i for i,x in enumerate(lows) if x[0]>=0};inactive={r:[i for i,(v,e) in enumerate(lows) if v<0 and e==r] for r in range(10)};tau=[]
 for i,(v,r) in enumerate(lows):
  if v>=0:tau.append(active[v^1,r^1])
  else:tau.append(inactive[r^1][inactive[r].index(i)])
 assert all(tau[tau[i]]==i and tau[i]!=i for i in range(50))
 forced={tuple(e) for e in a['forced_edges']};variables={tuple(v['edge']):i for i,v in enumerate(m['variables'])};new=[]
 def add(label,co,rhs):
  con={'label':label,'coefficients':co,'lower':rhs,'upper':rhs};m['constraints'].append(con);new.append(con)
 for pair,k in variables.items():
  image=tuple(sorted(tau[v] for v in pair))
  if image in variables:
   h=variables[image]
   if h>k:add('tau equality '+str((k,h)),[[k,1],[h,-1]],0)
  else:add('tau fixed image '+str(k),[[k,1]],int(image in forced))
 for pair in forced:
  image=tuple(sorted(tau[v] for v in pair))
  if image in variables:add('tau forced edge '+str(pair),[[variables[image],1]],1)
  elif image not in forced:add('tau missing forced image '+str(pair),[],1)
 m['low_tau']=tau;m['tau_constraints']=new;out.append(m)
r={'status':'COMPLETE','original_cap_seconds':30,'seconds':time.monotonic()-start,'records':out};(p/'models.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({'seconds':r['seconds'],'models':len(out),'equalities':sum(len(r['tau_constraints']) for r in out)}))
