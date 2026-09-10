import itertools,json
from pathlib import Path
out=[]
for omitted in [0,4,7,11]:
 G=[set() for _ in range(27)]
 def edge(u,v):G[u].add(v);G[v].add(u)
 masks=[7,25,10,18,12,20,1,1,4,16]
 for v,m in enumerate(masks,5):
  for c in range(5):
   if m>>c&1:edge(v,c)
 for u,v in [(5,8),(5,9),(6,7),(5,11),(6,12),(6,13),(6,14)]:edge(u,v)
 hosts={5:[0],7:[5,8],8:[1,2],9:[3,4],11:[5,6,7],12:[1,3,9],13:[2,6,10],14:[v for v in [0,4,7,11] if v!=omitted]}
 for v,empties in hosts.items():
  for e in empties:edge(v,15+e)
 for e in [8,9,10,11]:edge(15,15+e)
 violations=[(u,v,sorted(G[u]&G[v])) for u,v in itertools.combinations(range(27),2) if len(G[u]&G[v])>1]
 out.append(dict(omitted=omitted,c4_free=not violations,violations=violations,edges=[(u,v) for u in range(27) for v in G[u] if u<v]))
 print(omitted,'C4free',not violations,'violations',violations)
Path(__file__).with_name('patterns.json').write_text(json.dumps(out,indent=2)+'\n')
