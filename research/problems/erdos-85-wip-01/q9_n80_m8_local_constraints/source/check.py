from pathlib import Path
import itertools,json,collections,time
p=Path(__file__).parent;start=time.monotonic();internal=[(),(4,),(1,7),(3,5)];counts=collections.Counter();tested=0
fold=lambda x:min(x%8,(-x)%8)
for ai,sa in enumerate(internal):
 for bi,sb in enumerate(internal):
  for d in range(4):
   for T in itertools.combinations(range(8),d):
    adj=[set() for _ in range(16)]
    for x in range(8):
     for s in sa:adj[x].add((x+s)%8)
     for s in sb:adj[8+x].add(8+(x+s)%8)
     for t in T:adj[x].add(8+(x+t)%8);adj[8+(x+t)%8].add(x)
    tested+=1
    if any(len(adj[x]&adj[y])>1 for x in range(16) for y in range(x+1,16)):continue
    counts[ai,bi,d]+=1
    ds=[fold(x-y) for x,y in itertools.combinations(T,2)]
    assert 4 not in ds and len(ds)==len(set(ds))
    if d==3:assert set(ds)=={1,2,3} and len(sa)<2 and len(sb)<2
    if d and ai==bi:assert ai==0
    if d==2 and (len(sa)==2 or len(sb)==2):assert ds[0] in [1,3]
    if d and len(sa)==len(sb)==2:assert ai!=bi
r={'status':'PASS_LOCAL','tested':tested,'survivors':sum(counts.values()),'seconds':time.monotonic()-start,'pair_counts':[{'a':a,'b':b,'cross_degree':d,'count':n} for (a,b,d),n in sorted(counts.items())],'scope':'Local16-vertex lemma verification only; no full80-vertex search or quotient cover'}
(p/'results.json').write_text(json.dumps(r,indent=2)+'\n');print({k:v for k,v in r.items() if k!='pair_counts'})
