from pathlib import Path
import itertools as it,json,time,math
p=Path(__file__).resolve().parent;b=p.parent;start=time.monotonic();alloc=json.loads((b/'residual-ten-D5-five-311-fixed-allocation/results.json').read_text())['records'];graphs={r['root']:r for r in json.loads((b/'residual-ten-D5-five-311-high-matchings/results.json').read_text())['records']};pack=json.loads((b/'residual-ten-D5-five-311-packing/results.json').read_text())['records'];dom=json.loads((b/'residual-ten-D5-supports/results.json').read_text())['records'];out=[]
def flip(m):return sum(1<<(i^1) for i in range(10) if m>>i&1)
def guard():
 if time.monotonic()-start>=30:raise TimeoutError
pairs=list(it.combinations(range(10),2))
for source in alloc:
 if source['status']!='EXACT_RATIONAL_WITNESS':continue
 graph=graphs[source['packing_root']]['survivors'][source['graph']]
 if graph['edges']:continue
 guard();ci=source['class'];root=pack[ci]['survivors'][source['source_root']];c=dom[ci];R=[set() for _ in range(10)]
 for a,z in c['edges']:R[a].add(z);R[z].add(a)
 ss=[c['high3'][j] for j in root['high3']];S=[set(t) for s in ss for t in (s,[e^1 for e in s])];Z=[[int(i!=j and not R[i]&R[j] and not any(i in s and j in s for s in S)) for j in range(10)] for i in range(10)];D=[sum(Z[k][j] for k in R[i])-sum(Z[i][k] for k in R[j]) for i,j in pairs];target=tuple(root['q']+D);domains=[]
 for v in range(0,10,2):
  options=[]
  for m in graph['Q_domains'][v]:
   other=flip(m)
   if other not in graph['Q_domains'][v+1]:continue
   qs=[m,other];col=[sum((x>>e)&1 for x in qs) for e in range(10)];comm=[sum(((x>>i)&1)*(j in s)-(i in s)*((x>>j)&1) for x,s in zip(qs,S[v:v+2])) for i,j in pairs];options.append((m,tuple(col+comm)))
  domains.append(options)
 left={}
 for choices in it.product(*domains[:2]):
  key=tuple(map(sum,zip(*(x[1] for x in choices))));left.setdefault(key,[]).append([x[0] for x in choices])
 sols=[];right_count=0
 for choices in it.product(*domains[2:]):
  guard();right_count+=1;key=tuple(t-sum(vals) for t,vals in zip(target,zip(*(x[1] for x in choices))))
  for first in left.get(key,[]):
   rows=first+[x[0] for x in choices];full=[x for m in rows for x in (m,flip(m))];demand=[sum(e not in set().union(*(R[j] for j in s)) and not(m>>e&1) for m,s in zip(full,S)) for e in range(10)];low=[8-sum(e in s for s in S) for e in range(10)]
   assert demand==low
   sols.append(rows)
 out.append({'root':source['root'],'packing_root':source['packing_root'],'class':ci,'source_root':source['source_root'],'graph':source['graph'],'status':'COMPLETE','domain_sizes':list(map(len,domains)),'raw_products':math.prod(map(len,domains)),'left_keys':len(left),'right_products':right_count,'survivors':sols})
r={'status':'COMPLETE','original_cap_seconds':30,'seconds':time.monotonic()-start,'records':out};(p/'results.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({'seconds':r['seconds'],'roots':len(out),'raw_products':sum(r['raw_products'] for r in out),'positive_cases':sum(bool(r['survivors']) for r in out),'assignments':sum(len(r['survivors']) for r in out)}))
