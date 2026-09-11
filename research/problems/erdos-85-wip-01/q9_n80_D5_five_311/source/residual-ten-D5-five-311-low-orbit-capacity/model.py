from pathlib import Path
import json,itertools as it,time
p=Path(__file__).resolve().parent;b=p.parent;start=time.monotonic();old=json.loads((b/'residual-ten-D5-five-311-low-involution/models.json').read_text())['records'];prop={r['root']:r for r in json.loads((b/'residual-ten-D5-five-311-low-propagation/results.json').read_text())['records']};out=[]
for m in old:
 assert time.monotonic()-start<30
 a=next(x for x in prop[m['source_root']]['survivors'] if x['assignment']==m['assignment']);forced={tuple(e) for e in a['forced_edges']};lookup={tuple(v['edge']):k for k,v in enumerate(m['variables'])};tau=m['low_tau'];reps=[i for i in range(50) if i<tau[i]];cuts=[]
 for i,j in it.combinations(reps,2):
  pairs=[tuple(sorted((i,j))),tuple(sorted((i,tau[j])))];constant=sum(e in forced for e in pairs);co=[[lookup[e],1] for e in pairs if e in lookup]
  if not co and constant<=1:continue
  c={'label':'tau orbit capacity '+str((i,j)),'coefficients':sorted(co),'lower':-constant,'upper':1-constant};m['constraints'].append(c);cuts.append(c)
 m['orbit_capacity_cuts']=cuts;out.append(m)
r={'status':'COMPLETE','original_cap_seconds':30,'seconds':time.monotonic()-start,'records':out};(p/'models.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({'seconds':r['seconds'],'models':len(out),'cuts':sum(len(r['orbit_capacity_cuts']) for r in out)}))
