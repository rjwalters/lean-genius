from pathlib import Path
import itertools as it,json,time
p=Path(__file__).resolve().parent;start=time.monotonic()
patterns=list(it.combinations_with_replacement(range(4),5));patterns=[x for x in patterns if sum(x)==5]
single=[[(2*i,2*i+1)] for i in range(5)]
double=[[(2*i,2*j+t),(2*i+1,2*j+(t^1))] for i,j in it.combinations(range(5),2) for t in range(2)]
records=[];counts={str(x):0 for x in patterns}
for a in [1,3,5]:
 for singles in it.combinations(single,a):
  for doubles in it.combinations(double,(5-a)//2):
   assert time.monotonic()-start<30
   edges=sorted(tuple(sorted(e)) for o in singles+doubles for e in o);N=[set() for _ in range(10)]
   for u,v in edges:N[u].add(v);N[v].add(u)
   ds=tuple(sorted(len(N[2*i]) for i in range(5)))
   if max(ds)>3 or any(len(x&y)>1 for x,y in it.combinations(N,2)):continue
   seen=set();components=[]
   for v in range(10):
    if v in seen:continue
    todo=[v];vs=set()
    while todo:
     w=todo.pop()
     if w in vs:continue
     vs.add(w);todo.extend(N[w]-vs)
    seen|=vs;components.append(vs)
   assert all(sum(len(N[v]) for v in vs)//2==len(vs)-1 for vs in components)
   invariant=sorted((len(vs),tuple(sorted(len(N[v]) for v in vs)),{v^1 for v in vs}==vs) for vs in components)
   key=json.dumps(invariant);counts[str(ds)]+=1;records.append({'edges':edges,'pattern':ds,'key':key})
classes=[]
for key in sorted({r['key'] for r in records}):
 rs=[r for r in records if r['key']==key];classes.append({'key':key,'representative':rs[0]['edges'],'pattern':rs[0]['pattern'],'multiplicity':len(rs)})
out={'status':'COMPLETE','original_cap_seconds':30,'seconds':time.monotonic()-start,'patterns':patterns,'counts':counts,'classes':classes,'records':records};(p/'results.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:out[k] for k in ['status','seconds','counts','classes']}))
