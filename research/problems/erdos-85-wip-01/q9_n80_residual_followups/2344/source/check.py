from pathlib import Path
import itertools as it,json,time
start=time.monotonic();p=Path(__file__).resolve().parent;b=p.parent;classes=json.loads((b/'residual-ten-11123-supports/classes.json').read_text())['classes'];results=[]
def guard():
 if time.monotonic()-start>30:raise TimeoutError
try:
 for ci,cl in enumerate(classes):
  R=[set() for _ in range(10)]
  for a,bv in cl['representative_edges']:R[a].add(bv);R[bv].add(a)
  d=list(map(len,R));S3=[(frozenset(s),frozenset(v^1 for v in s)) for s in cl['support_orbits']];S2=[]
  for s in it.combinations(range(10),2):
   tau=tuple(sorted(v^1 for v in s))
   if s>tau or s[0]//2==s[1]//2 or sum(d[v] for v in s)>4:continue
   adj=[set(x) for x in R]+[set(s),set(tau)]
   for v in s:adj[v].add(10)
   for v in tau:adj[v].add(11)
   if all(len(adj[a]&adj[bv])<=1 for a in range(12) for bv in range(a)):S2.append((frozenset(s),frozenset(tau)))
  def compatible(a,bv):return all(len(x&y)<=1 for x in a for y in bv)
  for count3 in (1,2,3):
   rec={'class':ci,'n311':count3,'n_high2_orbits':7-2*count3,'status':'RUNNING','packings':0,'survivors':0,'first':None};results.append(rec)
   for triples in it.combinations(range(len(S3)),count3):
    guard();chosen3=[S3[i] for i in triples]
    if not all(compatible(a,bv) for a,bv in it.combinations(chosen3,2)):continue
    allowed=[i for i,a in enumerate(S2) if all(compatible(a,bv) for bv in chosen3)]
    for doubles in it.combinations(allowed,7-2*count3):
     guard();orbits=chosen3+[S2[i] for i in doubles]
     if not all(compatible(a,bv) for a,bv in it.combinations(orbits,2)):continue
     rec['packings']+=1;high=[s for a in orbits for s in a];ks=list(map(len,high));inc=[sum(r in s for s in high) for r in range(10)]
     if any(inc[r]>9-d[r] for r in range(10)):continue
     lower=0
     for r in range(10):
      low=9-d[r]-inc[r]
      if d[r]==3:continue
      supply=sum(k-1 for s,k in zip(high,ks) if not(R[r]&s) and (d[r]==1 or k==2))
      lower+=max(0,(3-d[r])*low-supply)
     for v,(sv,k) in enumerate(zip(high,ks)):
      base=k+2-sum(d[r] for r in sv);possible=[]
      for w,(sw,l) in enumerate(zip(high,ks)):
       if v==w or (k==3 and l==3):continue
       if any(R[r]&sw for r in sv):continue
       possible.append(l-1)
      extra=min(1,sum(possible)) if k==3 else sum(possible)
      lower+=max(0,base-extra)
     if lower>4*count3-2:continue
     rec['survivors']+=1
     if rec['first'] is None:rec['first']={'high3':[sorted(s) for a in chosen3 for s in a],'high2':[sorted(s) for i in doubles for s in S2[i]],'defect_lower_bound':lower}
   rec['status']='COMPLETE'
except TimeoutError:
 if results and results[-1]['status']=='RUNNING':results[-1]['status']='UNKNOWN'
result={'status':'COMPLETE' if len(results)==12 and all(r['status']=='COMPLETE' for r in results) else 'INCOMPLETE','original_cap_seconds':30,'seconds':time.monotonic()-start,'records':results}
(p/'results.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
