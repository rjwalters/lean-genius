from pathlib import Path
import json,itertools as it,time
p=Path(__file__).resolve().parent;b=p.parent;start=time.monotonic();data=json.loads((b/'residual-ten-D5-five-311-high-center-pairs/results.json').read_text())['records'];cross={r['root']:r for r in json.loads((b/'residual-ten-D5-five-311-center-cross-domains/results.json').read_text())['records']};out=[]
def guard():
 if time.monotonic()-start>=30:raise TimeoutError
try:
 for r in data:
  guard();c=cross[r['root']];high=[[sum(1<<v for v in g) for g in ds] for ds in c['high_groups']];low=[sum(1<<v for v in g['orbits']) for g in c['low_groups']];compat=[[sum(1<<i for i in xs) for xs in ds] for ds in c['compatibility']];pairs={(f,g,i,j):bits for f,g,i,j,bits in r['pair_domains']};rec={'root':r['root'],'status':'UNKNOWN','complete_assignments':0,'survivors':[]};out.append(rec)
  for E in it.combinations(list(it.combinations(range(5),2)),2):
   deg=[sum(v in e for e in E) for v in range(5)];options=[[i for i,d in enumerate(ds) if d==deg[f]] for f,ds in enumerate(r['degrees'])]
   def search(selected,used,allowed):
    guard()
    if len(selected)==5:
     rec['complete_assignments']+=1;remaining=((1<<25)-1)^used;ids=[i for i,m in enumerate(low) if allowed>>i&1 and m&remaining==m]
     if len(ids)<5 or not any(c['low_groups'][i]['inactive'] for i in ids) or sum(not c['low_groups'][i]['inactive'] for i in ids)<4:return
     union=0
     for i in ids:union|=low[i]
     if union!=remaining:return
     rec['survivors'].append({'high_edges':E,'high_options':[selected[f] for f in range(5)],'remaining':remaining,'low_options':ids});return
    choices=[]
    for f in range(5):
     if f in selected:continue
     ds=[]
     for i in options[f]:
      if high[f][i]&used:continue
      valid=True
      for g,j in selected.items():
       a,z=sorted((f,g));k,l=(i,j) if f<g else (j,i)
       if not pairs[a,z,k,l]&(2 if (a,z) in E else 1):valid=False;break
      if valid:ds.append(i)
     choices.append((f,ds))
    f,ds=min(choices,key=lambda x:len(x[1]))
    for i in ds:
     new=allowed&compat[f][i]
     if new.bit_count()<5:continue
     search({**selected,f:i},used|high[f][i],new)
   search({},0,(1<<len(low))-1)
  rec['status']='COMPLETE'
 status='COMPLETE'
except TimeoutError:status='INCOMPLETE'
seen={r['root'] for r in out}
for r in data:
 if r['root'] not in seen:out.append({'root':r['root'],'status':'UNVISITED'})
r={'status':status,'original_cap_seconds':30,'seconds':time.monotonic()-start,'records':out};(p/'results.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({'status':status,'seconds':r['seconds'],'complete':sum(r['status']=='COMPLETE' for r in out),'positive_cases':sum(bool(r.get('survivors')) for r in out),'assignments':sum(len(r.get('survivors',[])) for r in out),'before_low_filter':sum(r.get('complete_assignments',0) for r in out)}))
