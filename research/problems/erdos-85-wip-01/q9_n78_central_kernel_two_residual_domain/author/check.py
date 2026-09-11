from pathlib import Path
import itertools as I,json,time
p=Path(__file__).parent;start=time.monotonic();cap=30;source=p.parent/'n78-central-kernel-two-group-cover/results.json';models=json.loads(source.read_text())['models'];out=[]
def tick():
 if time.monotonic()-start>cap:raise TimeoutError
try:
 for mi,m in enumerate(models):
  tick();M=m['multiplication'];moves=m['X_action'];inverse=m['inverse'];seen=set();matchings=[]
  for a,b in I.combinations(range(8),2):
   if (a,b) in seen:continue
   E=sorted({tuple(sorted((mp[a],mp[b]))) for mp in moves});seen.update(E);deg=[0]*8
   for i,j in E:deg[i]+=1;deg[j]+=1
   if deg==[1]*8:matchings.append(E)
  conn=[d for d in I.combinations(range(1,16),2) if set(map(inverse.__getitem__,d))==set(d)]
  r={'model':mi,'status':'RUNNING','matchings':matchings,'connections':conn,'tested':0,'survivors':[]};out.append(r)
  for ei,E in enumerate(matchings):
   for di,D in enumerate(conn):
    for origin in range(8):
     tick();edges=set(E)
     for g in range(16):
      edges.add((moves[g][origin],8+g))
      for d in D:edges.add(tuple(sorted((8+g,8+M[g][d]))))
     N=[set() for _ in range(24)]
     for a,b in edges:N[a].add(b);N[b].add(a)
     assert [len(x) for x in N]==[3]*24;r['tested']+=1
     if any(len(N[a]&N[b])>1 for a,b in I.combinations(range(24),2)):continue
     r['survivors'].append({'matching':ei,'connection':di,'origin':origin,'edges':sorted(edges)})
  r['status']='COMPLETE'
 status='COMPLETE'
except TimeoutError:
 status='INCOMPLETE'
 if out and out[-1]['status']=='RUNNING':out[-1]['status']='UNKNOWN'
 for mi in range(len(out),len(models)):out.append({'model':mi,'status':'UNVISITED'})
r={'status':status,'original_cap_seconds':cap,'seconds':time.monotonic()-start,'records':out};(p/'results.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({'status':status,'seconds':r['seconds'],'counts':[(x['model'],x['status'],len(x.get('matchings',[])),len(x.get('connections',[])),x.get('tested'),len(x.get('survivors',[]))) for x in out]}))
