from pathlib import Path
import itertools,json,hashlib
p=Path(__file__).resolve().parent;source=p.parent/'q9-order3-color-lp-cover/receipts.jsonl';cases=[r for r in map(json.loads,source.read_text().splitlines()) if r['status']=='EXACT_FRACTIONAL_FEASIBLE'];ps=list(itertools.permutations(range(3)));pairs=list(itertools.combinations(range(5),2));words=list(itertools.product(range(3),repeat=5))
with (p/'input.txt').open('w') as f:
 f.write(str(len(cases))+'\n')
 for r in cases:
  z=r['code'];digits=[0]*10
  for i in range(9,-1,-1):digits[i]=z%6;z//=6
  P={}
  for (u,v),z in zip(pairs,digits):P[u,v]=ps[z];P[v,u]=tuple(ps[z].index(a) for a in range(3))
  U={(u,v,a,b):3-int(a!=0 and P[u,v][3-a]==b)-int(P[u,v][a]!=0 and 3-P[u,v][a]==b)-sum(P[t,v][P[u,t][a]]==b for t in range(5) if t not in (u,v)) for u,v in pairs for a in range(3) for b in range(3)}
  ids=[]
  for i,w in enumerate(words):
   if not all(U[u,v,w[u],w[v]]>0 for u,v in pairs):continue
   if not all(3-int(w[u]!=0 and a==3-w[u])-sum(P[v,u][w[v]]==a for v in range(5) if v!=u)>=0 for u in range(5) for a in range(3)):continue
   ids.append(i)
  f.write(' '.join(map(str,[r['code'],len(ids),*ids,*[U[u,v,a,b] for u,v in pairs for a in range(3) for b in range(3)]]))+'\n')
(p/'launch.json').write_text(json.dumps({'original_total_wall_cap_seconds':60,'original_node_cap_per_case':100000,'cases':len(cases),'scope':'first ten-word selection per surviving permutation; no Q/lift','retry':False,'input_source_sha256':hashlib.sha256(source.read_bytes()).hexdigest()},indent=2)+'\n')
