import itertools,json,time
from pathlib import Path
p=Path(__file__).parent;start=time.monotonic();counts={};records=[]
for k in (2,3):
 for domain in itertools.combinations(range(3),k):
  for target in itertools.permutations(range(3),k):
   mapping=[-1]*3
   for a,b in zip(domain,target):mapping[a]=b
   es=[(1,2),(4,5)]+[(a,3+b) for a,b in zip(domain,target)]
   cycle=set(mapping[1:])=={1,2};valid=0;bad=0
   for shifts in itertools.product(range(3),repeat=len(es)):
    assert time.monotonic()-start<60
    adj=[set() for _ in range(20)]
    def edge(u,v):adj[u].add(v);adj[v].add(u)
    for label in range(6):
     for g in range(3):edge(0 if label<3 else 1,2+3*label+g)
    for (a,b),s in zip(es,shifts):
     for g in range(3):edge(2+3*a+g,2+3*b+(g+s)%3)
    c4=any(len(adj[u]&adj[v])>=2 for u,v in itertools.combinations(range(20),2))
    if c4:bad+=1
    else:valid+=1
   assert bad==(3**(len(es)-1) if cycle else 0)
   records.append({'cross_orbits':k,'mapping':mapping,'has_cycle':cycle,'valid':valid,'c4':bad})
result={'status':'COMPLETE','original_wall_cap':60,'seconds':time.monotonic()-start,'rooted_matchings':len(records),'assignments':sum(x['valid']+x['c4'] for x in records),'c4_free':sum(x['valid'] for x in records),'c4':sum(x['c4'] for x in records),'records':records}
(p/'results.json').write_text(json.dumps(result,indent=2)+'\n');print({k:v for k,v in result.items() if k!='records'})
