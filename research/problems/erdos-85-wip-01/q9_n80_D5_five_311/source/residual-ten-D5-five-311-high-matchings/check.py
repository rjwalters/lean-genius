from pathlib import Path
import json,itertools as it,time
p=Path(__file__).resolve().parent;b=p.parent;start=time.monotonic();alloc=json.loads((b/'residual-ten-D5-five-311-allocation/results.json').read_text())['records'];pack=json.loads((b/'residual-ten-D5-five-311-packing/results.json').read_text())['records'];domain=json.loads((b/'residual-ten-D5-supports/results.json').read_text())['records'];out=[]
def guard():
 if time.monotonic()-start>=30:raise TimeoutError
try:
 for source in alloc:
  if source['status']!='EXACT_RATIONAL_WITNESS':continue
  guard();ci=source['class'];ri=source['source_root'];root=pack[ci]['survivors'][ri];c=domain[ci];R=[set() for _ in range(10)]
  for a,z in c['edges']:R[a].add(z);R[z].add(a)
  assert all(len(x)==1 for x in R)
  ss=[c['high3'][i] for i in root['high3']];S=[set(t) for s in ss for t in (s,[v^1 for v in s])];middle=[set().union(*(R[e] for e in s)) for s in S];low=[8-sum(e in s for s in S) for e in range(10)];q=root['q'];assert min(low)>0
  allowed={(v,w) for v in range(10) for w in range(10) if v!=w and not middle[v]&S[w]}
  def matchings(rem,H):
   guard()
   if not rem:yield H;return
   v=min(rem);rest=rem-{v,v^1}
   yield from matchings(rest,H)
   if (v,v^1) in allowed:yield from matchings(rest,H+[(v,v^1)])
   for w in sorted(rest):
    if (v,w) in allowed and (v^1,w^1) in allowed:yield from matchings(rest-{w,w^1},H+[(v,w),(v^1,w^1)])
  rec={'root':source['root'],'class':ci,'source_root':ri,'status':'UNKNOWN','matchings':0,'survivors':[]};out.append(rec)
  for edges in matchings(set(range(10)),[]):
   rec['matchings']+=1;H=[set() for _ in range(10)]
   for v,w in edges:H[v].add(w);H[w].add(v)
   ds=[];forced_low=[0]*10
   for v in range(10):
    covered=middle[v]|set().union(*(S[w] for w in H[v]));assert len(covered)==3+3*len(H[v])
    choices=[sum(1<<e for e in Q) for Q in it.combinations([e for e in range(10) if e not in covered and q[e]>0],2-2*len(H[v]))]
    ds.append(choices)
    for e in range(10):
     if e not in covered and all(not(m>>e&1) for m in choices):forced_low[e]+=1
   if any(not x for x in ds):continue
   forced=[sum(all(m>>e&1 for m in d) for d in ds) for e in range(10)]
   if any(x>y for x,y in zip(forced,q)) or any(x>y for x,y in zip(forced_low,low)):continue
   rec['survivors'].append({'edges':edges,'Q_domains':ds})
  rec['status']='COMPLETE'
 status='COMPLETE'
except TimeoutError:status='INCOMPLETE'
seen={r['root'] for r in out}
for r in alloc:
 if r['status']=='EXACT_RATIONAL_WITNESS' and r['root'] not in seen:out.append({'root':r['root'],'class':r['class'],'source_root':r['source_root'],'status':'UNVISITED'})
r={'status':status,'original_cap_seconds':30,'seconds':time.monotonic()-start,'records':out};(p/'results.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({'status':status,'seconds':r['seconds'],'roots':len(out),'matchings':sum(r.get('matchings',0) for r in out),'positive_roots':sum(bool(r.get('survivors')) for r in out),'surviving_matchings':sum(len(r.get('survivors',[])) for r in out)}))
