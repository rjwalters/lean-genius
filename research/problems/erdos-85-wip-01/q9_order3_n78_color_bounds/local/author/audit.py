from itertools import product,permutations,combinations
from pathlib import Path
import json,time
p=Path(__file__).resolve().parent;start=time.monotonic();ps=list(permutations(range(3)));pairs=list(combinations(range(3),2));words=list(product(range(3),repeat=3));out=[]
for code,ds in enumerate(product(range(6),repeat=3)):
 if time.monotonic()-start>60:break
 P={}
 for (u,v),k in zip(pairs,ds):P[u,v]=ps[k];P[v,u]=tuple(ps[k].index(a) for a in range(3))
 caps={}
 for u,v in pairs:
  t=3-u-v
  for a,b in product(range(3),repeat=2):caps[u,v,a,b]=3-int(a!=0 and P[u,v][3-a]==b)-int(P[u,v][a]!=0 and 3-P[u,v][a]==b)-int(P[t,v][P[u,t][a]]==b)
 records=[]
 for w in words:
  B=[[3-int(w[u]!=0 and a==3-w[u])-sum(P[v,u][w[v]]==a for v in range(3) if v!=u) for a in range(3)] for u in range(3)]
  bound=min([3]+[caps[u,v,w[u],w[v]] for u,v in pairs])
  if any(x<0 for row in B for x in row):bound=0
  if any(w[u]!=0 and B[u]!=[2,2,2] for u in range(3)):bound=min(bound,2)
  records.append({'word':w,'multiplicity_upper_bound':bound,'B':B})
 out.append({'code':code,'permutations':ds,'status':'COMPLETE','words':records})
summary={'cases_complete':len(out),'cases_unvisited':216-len(out),'original_wall_cap_seconds':60,'seconds':time.monotonic()-start,'word_triple_counts_by_nonzero':{str(k):sum(r['multiplicity_upper_bound']==3 and sum(x!=0 for x in r['word'])==k for c in out for r in c['words']) for k in range(4)},'cases_with_no_triple_words':sum(not any(r['multiplicity_upper_bound']==3 for r in c['words']) for c in out),'scope':'local necessary bounds, no graph or complete quotient search'}
(p/'results.json').write_text(json.dumps(out,indent=2)+'\n');(p/'summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary))
