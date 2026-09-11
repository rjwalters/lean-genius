from pathlib import Path
import json,time,itertools as it,functools
p=Path(__file__).resolve().parent;b=p.parent;start=time.monotonic();data=json.loads((b/'residual-ten-D5-five-311-center-cross-domains/results.json').read_text())['records'];out=[]
def guard():
 if time.monotonic()-start>=30:raise TimeoutError
@functools.lru_cache(None)
def center_graph(patterns):
 cross=[(v,5+j) for j,A in enumerate(patterns) for v in range(5) if not A>>v&1];d=[sum(v in e for e in cross) for v in range(5)];ones=[5+j for j,A in enumerate(patterns) if A.bit_count()==3]
 if len(ones)!=4 or max(d)>3:return None
 lowmatch=[[(ones[0],ones[1]),(ones[2],ones[3])],[(ones[0],ones[2]),(ones[1],ones[3])],[(ones[0],ones[3]),(ones[1],ones[2])]]
 for high in it.combinations(list(it.combinations(range(5),2)),2):
  if any(d[v]+sum(v in e for e in high)!=3 for v in range(5)):continue
  for lm in lowmatch:
   E=cross+list(high)+lm;N=[set() for _ in range(10)]
   for v,w in E:N[v].add(w);N[w].add(v)
   if all(len(x&y)<=1 for x,y in it.combinations(N,2)):return E
 return None
try:
 for r in data:
  guard();low=[(sum(1<<v for v in x['orbits']),x['active'],x['inactive']) for x in r['low_groups']];high=[[(sum(1<<v for v in g),sum(1<<li for li in r['compatibility'][i][j])) for j,g in enumerate(ds)] for i,ds in enumerate(r['high_groups'])];by=[[i for i,x in enumerate(low) if x[0]>>v&1] for v in range(25)];rec={'root':r['root'],'status':'UNKNOWN'};out.append(rec)
  @functools.lru_cache(None)
  def lowcover(rem,patterns,z,allowed):
   guard()
   if not rem:
    if z!=1:return None
    graph=center_graph(patterns)
    return ((),graph) if graph is not None else None
   choices=min(([i for i in by[v] if allowed>>i&1 and low[i][0]&rem==low[i][0] and z+low[i][2]<=1 and all(((31^low[i][1])&(31^A)).bit_count()<=1 for A in patterns)] for v in range(25) if rem>>v&1),key=len)
   for li in choices:
    m,A,dz=low[li];newpatterns=patterns+(A,)
    if any(sum(not X>>v&1 for X in newpatterns)>3 for v in range(5)):continue
    tail=lowcover(rem^m,newpatterns,z+dz,allowed)
    if tail is not None:return ((li,)+tail[0],tail[1])
   return None
  @functools.lru_cache(None)
  def cover(pending,used,allowed):
   guard()
   if allowed.bit_count()<5:return None
   if not pending:
    tail=lowcover(((1<<25)-1)^used,(),0,allowed)
    return ((),tail) if tail is not None else None
   choices=[(i,[(j,m,allowed&ok) for j,(m,ok) in enumerate(high[i]) if not m&used and (allowed&ok).bit_count()>=5]) for i in range(5) if pending>>i&1];i,ds=min(choices,key=lambda x:len(x[1]))
   for j,m,newallowed in ds:
    tail=cover(pending^(1<<i),used|m,newallowed)
    if tail is not None:return (((i,j),)+tail[0],tail[1])
   return None
  witness=cover(31,0,(1<<len(low))-1);rec.update(status='COMPLETE',high_states=cover.cache_info().currsize,low_states=lowcover.cache_info().currsize,witness=witness)
 status='COMPLETE'
except TimeoutError:status='INCOMPLETE'
seen={r['root'] for r in out}
for r in data:
 if r['root'] not in seen:out.append({'root':r['root'],'status':'UNVISITED'})
r={'status':status,'original_cap_seconds':30,'seconds':time.monotonic()-start,'records':out};(p/'results.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({'status':status,'seconds':r['seconds'],'complete':sum(x['status']=='COMPLETE' for x in out),'negative':sum(x['status']=='COMPLETE' and x['witness'] is None for x in out),'positive':sum(x['status']=='COMPLETE' and x['witness'] is not None for x in out)}))
