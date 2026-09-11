from pathlib import Path
import itertools as it,json,time
p=Path(__file__).resolve().parent;start=time.monotonic();data=json.loads((p.parent/'residual-ten-D5-shapes/results.json').read_text());out=[]
def graph(edges,supports):
 N=[set() for _ in range(10+len(supports))]
 for a,b in edges:N[a].add(b);N[b].add(a)
 for v,s in enumerate(supports,10):
  for e in s:N[v].add(e);N[e].add(v)
 return N
def good(N):return all(len(a&b)<=1 for a,b in it.combinations(N,2))
for ci,c in enumerate(data['classes']):
 R=graph(c['representative'],[]);rec={'class':ci,'edges':c['representative'],'pattern':c['pattern']};domains={}
 for k in [2,3]:
  ds=[]
  for s in it.combinations(range(10),k):
   assert time.monotonic()-start<30
   other=tuple(sorted(v^1 for v in s))
   if s>other or sum(len(R[e]) for e in s)>k+2:continue
   if good(graph(c['representative'],[s,other])):ds.append(s)
  rec['high'+str(k)]=ds;domains[k]=ds
 pairs={}
 for k,l in [(2,2),(2,3),(3,3)]:
  yes=[]
  for i,s in enumerate(domains[k]):
   for j,t in enumerate(domains[l]):
    assert time.monotonic()-start<30
    if k==l and i>=j:continue
    ss=[s,tuple(v^1 for v in s),t,tuple(v^1 for v in t)]
    if good(graph(c['representative'],ss)):yes.append([i,j])
  pairs[str(k)+str(l)]=yes
 rec['compatible_pairs']=pairs;out.append(rec)
r={'status':'COMPLETE','original_cap_seconds':30,'seconds':time.monotonic()-start,'records':out};(p/'results.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({'status':r['status'],'seconds':r['seconds'],'counts':[{'class':x['class'],'high2':len(x['high2']),'high3':len(x['high3']),'pairs':{k:len(v) for k,v in x['compatible_pairs'].items()}} for x in out]}))
