from pathlib import Path
import itertools,json,hashlib
P=Path(__file__).parent;source=P/'results.json';data=json.loads(source.read_text());assert data['status']=='COMPLETE';rows=[]
for i,r in enumerate(data['classes']):
 g=[set() for _ in range(14)]
 def add(u,v):g[u].add(v);g[v].add(u)
 for u,v in r['edges']:add(u,v)
 next_leaf=7
 for u,n in enumerate(r['leaf_attachment_counts']):
  for _ in range(n):add(u,next_leaf);next_leaf+=1
 assert 14-next_leaf==2*r['leaf_leaf_edges']
 for u in range(next_leaf,14,2):add(u,u+1)
 assert list(map(len,g))==[3]*7+[1]*7
 count=0;sample=None
 for assignment in itertools.permutations(range(7,14)):
  if any(g[u]&g[v] for u,v in enumerate(assignment)):continue
  count+=1
  if sample is None:sample=assignment
 assert count>0
 # Directly check a full high+singleton partial graph for the retained witness.
 witness=[set(ns) for ns in g]+[set() for _ in range(7)]
 for u,v in enumerate(sample):
  h=14+u;witness[h].update([u,v]);witness[u].add(h);witness[v].add(h)
 assert all(len(witness[u]&witness[v])<=1 for u in range(21) for v in range(u))
 rows.append({'core_index':i,'singleton_edges':[[u,v] for u in range(14) for v in sorted(g[u]) if u<v],'colour_pairings':count,'witness_leaf_assignment':sample})
r={'status':'COMPLETE','source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'bijections_tested':len(rows)*5040,'all_classes_survive':True,'rows':rows,'scope':'Conditional exact high colour pairing count per fixed singleton shape. No quotient by automorphisms, no empty/pair completion or full H7 exclusion.'}
(P/'colour-results.json').write_text(json.dumps(r,indent=2)+'\n');print({k:v for k,v in r.items() if k!='rows'})
