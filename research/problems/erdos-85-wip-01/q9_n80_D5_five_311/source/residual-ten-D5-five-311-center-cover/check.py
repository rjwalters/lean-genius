from pathlib import Path
import json,time,functools
p=Path(__file__).resolve().parent;b=p.parent;start=time.monotonic();data=json.loads((b/'residual-ten-D5-five-311-center-domains/results.json').read_text())['records'];out=[]
def guard():
 if time.monotonic()-start>=30:raise TimeoutError
try:
 for r in data:
  guard();high=[[sum(1<<v for v in g) for g in ds] for ds in r['high_groups']];low=[sum(1<<v for v in g) for g in r['low_groups']];by=[[m for m in low if m>>v&1] for v in range(25)]
  @functools.lru_cache(None)
  def lowcover(rem):
   guard()
   if not rem:return ()
   choices=min(([m for m in by[v] if m&rem==m] for v in range(25) if rem>>v&1),key=len)
   for m in choices:
    tail=lowcover(rem^m)
    if tail is not None:return (m,)+tail
   return None
  @functools.lru_cache(None)
  def cover(pending,used):
   guard()
   if not pending:
    tail=lowcover(((1<<25)-1)^used)
    return ((),tail) if tail is not None else None
   options=[(i,[m for m in high[i] if not m&used]) for i in range(5) if pending>>i&1];i,ds=min(options,key=lambda x:len(x[1]))
   for m in ds:
    tail=cover(pending^(1<<i),used|m)
    if tail is not None:return (((i,m),)+tail[0],tail[1])
   return None
  witness=cover(31,0);rec={'root':r['root'],'status':'COMPLETE','high_states':cover.cache_info().currsize,'low_states':lowcover.cache_info().currsize,'witness':witness}
  if witness is not None:
   masks=[m for i,m in witness[0]]+list(witness[1]);assert len(masks)==10 and sum(m.bit_count() for m in masks)==25 and sum(masks)==(1<<25)-1
  out.append(rec)
 status='COMPLETE'
except TimeoutError:status='INCOMPLETE'
seen={r['root'] for r in out}
for r in data:
 if r['root'] not in seen:out.append({'root':r['root'],'status':'UNVISITED'})
r={'status':status,'original_cap_seconds':30,'seconds':time.monotonic()-start,'records':out};(p/'results.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({'status':status,'seconds':r['seconds'],'negative':sum(x['status']=='COMPLETE' and x['witness'] is None for x in out),'positive':sum(x['status']=='COMPLETE' and x['witness'] is not None for x in out)}))
