from pathlib import Path
import itertools as it,json,time
p=Path(__file__).parent;start=time.monotonic();status='INCOMPLETE';records=[];counts={'base':0,'W0':0,'W2':0,'positive':0}
def guard():
 if time.monotonic()-start>30:raise TimeoutError
def mul(a,b):
 i,j=divmod(a,2);k,l=divmod(b,2);return 2*((i+pow(3,j)*k)%8)+(j^l)
inv=[next(b for b in range(16) if mul(a,b)==0) for a in range(16)]
def edge(N,a,b):N[a].add(b);N[b].add(a)
def c4(N):
 seen={}
 for v,ns in enumerate(N):
  for a,b in it.combinations(sorted(ns),2):
   if (a,b) in seen:return [a,seen[a,b],b,v]
   seen[a,b]=v
 return None
connections=[]
for pair in it.combinations(range(1,16),2):
 if {inv[a] for a in pair}!=set(pair):continue
 N=[set() for _ in range(16)]
 for g in range(16):
  for a in pair:edge(N,g,mul(g,a))
 unseen=set(range(16));sizes=[]
 while unseen:
  todo=[min(unseen)];component=set()
  while todo:
   v=todo.pop()
   if v in component:continue
   component.add(v);todo.extend(N[v]-component)
  unseen-=component;sizes.append(len(component))
 if sorted(sizes)==[8,8]:connections.append(pair)
triples=[(0,a,b) for a,b in it.combinations(range(1,16),2)]
try:
 for u in [0,1]:
  pairs=[d for d in range(16) if (u*(d//2)+d%2)%2==1]
  for T in connections:
   guard();base=[set() for _ in range(24)]
   for g in range(16):
    for h in T:edge(base,8+g,8+mul(g,h))
    edge(base,g//2,8+g);edge(base,g//2,mul(g,8)//2)
   bad=c4(base);counts['base']+=1
   if bad:records.append({'u':u,'T':T,'stage':'base','c4':bad});continue
   for d,x in it.product(pairs,range(8)):
    guard();N=[set(ns) for ns in base]+[set() for _ in range(16)]
    for g in range(16):
     edge(N,24+g,mul(g,2*x)//2);edge(N,24+g,8+g);edge(N,24+g,8+mul(g,d))
    bad=c4(N);counts['W0']+=1
    if bad:records.append({'u':u,'T':T,'d':d,'x':x,'stage':'W0','c4':bad});continue
    for D in triples:
     guard();B=[set(ns) for ns in N]+[set() for _ in range(16)]
     for g in range(16):
      for h in D:edge(B,40+g,8+mul(g,h))
     bad=c4(B);counts['W2']+=1;counts['positive']+=bad is None
     records.append({'u':u,'T':T,'d':d,'x':x,'D':D,'stage':'W2','c4':bad})
 status='COMPLETE'
except TimeoutError:pass
result={'status':status,'original_cap_seconds':30,'seconds':time.monotonic()-start,'connections':connections,'triples':triples,'counts':counts,'records':records}
(p/'results.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:result[k] for k in ['status','seconds','connections','counts']}))
