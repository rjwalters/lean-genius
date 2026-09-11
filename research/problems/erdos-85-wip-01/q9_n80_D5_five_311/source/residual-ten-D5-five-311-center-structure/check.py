from pathlib import Path
import itertools as it,json,time
p=Path(__file__).resolve().parent;start=time.monotonic();out=[];T={0,1,2};available=[pair for pair in it.combinations(range(5),2) if not set(pair)<=T];lowmatch=[[(6,7),(8,9)],[(6,8),(7,9)],[(6,9),(7,8)]];tested=0
for four in it.combinations(available,4):
 cross=[(v,5) for v in T]+[(v,6+i) for i,pair in enumerate(four) for v in pair];degree=[sum(v in e for e in cross) for v in range(5)]
 for high in it.combinations(list(it.combinations(range(5),2)),2):
  if any(degree[v]+sum(v in e for e in high)!=3 for v in range(5)):continue
  for low in lowmatch:
   assert time.monotonic()-start<30
   tested+=1;edges=sorted(tuple(sorted(e)) for e in cross+list(high)+low);N=[set() for _ in range(10)]
   for v,w in edges:N[v].add(w);N[w].add(v)
   assert all(len(ns)==3 for ns in N)
   if any(len(a&b)>1 for a,b in it.combinations(N,2)):continue
   out.append({'edges':edges,'high_edges':high,'low_edges':low,'low_high_neighbors':[sorted(T)]+[list(e) for e in four]})
r={'status':'COMPLETE','original_cap_seconds':30,'seconds':time.monotonic()-start,'tested_degree_compatible':tested,'records':out};(p/'results.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({'seconds':r['seconds'],'degree_compatible':tested,'survivors':len(out),'high_shapes':{str(sorted(sum(v in e for e in r['high_edges']) for v in range(5))):sum(sorted(sum(v in e for e in q['high_edges']) for v in range(5))==sorted(sum(v in e for e in r['high_edges']) for v in range(5)) for q in out) for r in out}}))
