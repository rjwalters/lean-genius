import json,hashlib,itertools,pathlib
P=pathlib.Path('/Users/rwalters/lean-genius-q7-outside-first-20260910/core44-colour0-structure'); O=pathlib.Path(__file__).parent
pins=json.loads((P/'pins.json').read_text())
for f,h in pins.items():assert hashlib.sha256((P/f).read_bytes()).hexdigest()==h,f
rows=json.loads((P/'skeletons.json').read_text())['results']; audits=[]
for row in rows:
 g=[set() for _ in range(35)]
 def edge(u,v):g[u].add(v);g[v].add(u)
 for v,cs in enumerate([(0,1,2),(0,3,4),(1,3),(1,4),(2,3),(2,4)],5):
  for c in cs:edge(v,c)
 for a,b in [(5,8),(5,9),(6,7)]:edge(a,b)
 for h,es in [(5,[0]),(7,[5,8]),(8,[1,2]),(9,[3,4])]:
  for e in es:edge(h,11+e)
 for e in [8,9,10,11]:edge(11,11+e)
 for v,c,h,es in [(23,0,5,[5,6,7]),(24,0,6,[1,3,9]),(25,2,6,[2,6,10]),(26,4,6,[e for e in [0,4,7,11] if e!=row['omitted']])]:
  edge(v,c);edge(v,h)
  for e in es:edge(v,11+e)
 for i in range(5):edge(27+i,i);edge(27+i,10)
 edge(29,7)
 for a,b in row['internal']:edge(27+a,27+b)
 if row['af'] is not None:edge(23,27+row['af'])
 if row['bf'] is not None:edge(24,27+row['bf'])
 for v in range(32,35):edge(0,v)
 # Exhaust every labelled S0 matching and f2/f3 target. No canonical labels assumed.
 solutions=[]
 for mate in range(32,35):
  others=[v for v in range(32,35) if v!=mate]
  matching=[(27,mate),tuple(others)]
  for t2,t3 in itertools.product(range(32,35),repeat=2):
   q=[s.copy() for s in g]
   for u,v in matching+[(29,t2),(30,t3)]:q[u].add(v);q[v].add(u)
   if any(len(q[u]&q[v])>1 for u,v in itertools.combinations(range(35),2)):continue
   solutions.append((mate,t2,t3))
 assert len(solutions)==6 and all(len(set(s))==3 for s in solutions)
 # Every surviving labelling uniquely renames to gA,gB,gC.
 for u,v in [(27,32),(29,33),(33,34),(30,34)]:edge(u,v)
 slots=[]
 for c in range(1,5):
  for host in [23,24,27,32,33,34]:
   if any(x in g[c] for x in g[host]):continue
   v=len(g);g.append(set());edge(v,c);edge(v,host);slots.append({'vertex':v,'colour':c,'host':host})
 assert slots==row['slots'] and [sorted(s) for s in g]==row['adjacency']
 assert len(g)==49 and all(len(g[u]&g[v])<=1 for u,v in itertools.combinations(range(49),2))
 assert all(len(g[v]&g[0])==1 for v in list(range(1,11))+list(range(23,49)))
 missing=[v for v in range(11,23) if not(g[v]&g[0])]
 assert len(missing)==5
 deficits={v:7-len(g[v]) for v in [27,32,33,34]}
 assert deficits=={27:2,32:1,33:1,34:1}
 audits.append({'omitted':row['omitted'],'internal':row['internal'],'labelled_namings':len(solutions),'missing_empty_slots':missing,'deficits':deficits})
for f,h in pins.items():assert hashlib.sha256((P/f).read_bytes()).hexdigest()==h,f
out={'status':'PASS','scope':'Necessary canonical relabelling only; no completion or exclusion','pinned_payloads':len(pins),'independently_rebuilt_skeletons':len(audits),'results':audits}
(O/'results.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
