from pathlib import Path
import json,time,itertools as it,functools
p=Path(__file__).resolve().parent;b=p.parent;start=time.monotonic();data=json.loads((b/'residual-ten-D5-five-311-center-domains/results.json').read_text())['records'];prior={r['root']:r for r in json.loads((b/'residual-ten-D5-five-311-center-cover/results.json').read_text())['records']};lowcases={r['root']:r for r in json.loads((b/'residual-ten-D5-five-311-low-edge-capacity/results.json').read_text())['records']};out=[]
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
  if prior[r['root']]['witness'] is None:continue
  guard();lows=next(a['lows'] for a in lowcases[r['source_root']]['survivors'] if a['assignment']==r['source_assignment']);colors=[lows[pair[0]][0]//2 if lows[pair[0]][0]>=0 else -1 for pair in r['low_orbits']];high=[[sum(1<<v for v in g) for g in ds] for ds in r['high_groups']];low=[]
  for g in r['low_groups']:
   cs=[colors[v] for v in g];z=cs.count(-1);A=sum(1<<v for v in set(cs) if v>=0)
   if z<=1 and A.bit_count()==3-z:low.append((sum(1<<v for v in g),A,z))
  by=[[x for x in low if x[0]>>v&1] for v in range(25)];rec={'root':r['root'],'status':'UNKNOWN','low_options':len(low)};out.append(rec)
  @functools.lru_cache(None)
  def lowcover(rem,patterns,z):
   guard()
   if not rem:
    if z!=1:return None
    graph=center_graph(patterns)
    return ((),graph) if graph is not None else None
   choices=min(([x for x in by[v] if x[0]&rem==x[0] and z+x[2]<=1 and all(((31^x[1])&(31^A)).bit_count()<=1 for A in patterns)] for v in range(25) if rem>>v&1),key=len)
   for m,A,dz in choices:
    newpatterns=patterns+(A,)
    if any(sum(not X>>v&1 for X in newpatterns)>3 for v in range(5)):continue
    tail=lowcover(rem^m,newpatterns,z+dz)
    if tail is not None:return ((m,)+tail[0],tail[1])
   return None
  @functools.lru_cache(None)
  def cover(pending,used):
   guard()
   if not pending:
    tail=lowcover(((1<<25)-1)^used,(),0)
    return ((),tail) if tail is not None else None
   i,ds=min([(i,[m for m in high[i] if not m&used]) for i in range(5) if pending>>i&1],key=lambda x:len(x[1]))
   for m in ds:
    tail=cover(pending^(1<<i),used|m)
    if tail is not None:return (((i,m),)+tail[0],tail[1])
   return None
  witness=cover(31,0);rec.update(status='COMPLETE',high_states=cover.cache_info().currsize,low_states=lowcover.cache_info().currsize,witness=witness)
 status='COMPLETE'
except TimeoutError:status='INCOMPLETE'
seen={r['root'] for r in out}
for r in data:
 if prior[r['root']]['witness'] is not None and r['root'] not in seen:out.append({'root':r['root'],'status':'UNVISITED'})
r={'status':status,'original_cap_seconds':30,'seconds':time.monotonic()-start,'records':out};(p/'results.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({'status':status,'seconds':r['seconds'],'complete':sum(x['status']=='COMPLETE' for x in out),'negative':sum(x['status']=='COMPLETE' and x['witness'] is None for x in out),'positive':sum(x['status']=='COMPLETE' and x['witness'] is not None for x in out)}))
