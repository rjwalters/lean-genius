from pathlib import Path
import json,hashlib,itertools,collections,time
P=Path('/Users/rwalters/lean-genius-q7-outside-first-20260910/h7-a7-empty-first');O=Path(__file__).parent;start=time.monotonic()
pins=json.loads((P/'pins.json').read_text())
for f,h in pins.items():assert hashlib.sha256((P/f).read_bytes()).hexdigest()==h
fixtures=json.loads((P/'results.json').read_text())['fixtures'];K=list(itertools.combinations(range(7),2));Fcases=[{tuple(sorted((i,(i+1)%7))) for i in range(7)},{(0,1),(0,2),(1,2),(3,4),(3,5),(4,5),(5,6)}];out=[]
for r in fixtures:
 phi={tuple(e):x for e,x in r['phi']};F=Fcases[r['F_case']];fg=[set() for _ in range(7)]
 for u,v in F:fg[u].add(v);fg[v].add(u)
 assert len(phi)==14 and sorted(collections.Counter(phi.values()).values())==sorted(map(len,fg))
 unused=[]
 for i in range(7):
  used=[x for e,x in phi.items() if i in e];assert len(used)==len(set(used))==4
  unused.append(sorted(set(range(7))-set(used)))
 assert unused==r['unused']
 allowed=[{tuple(x for x in U if x!=single) for single in U if not fg[next(x for x in U if x!=single)]&fg[next(x for x in reversed(U) if x!=single)]} for U in unused]
 hall=all(len(set().union(*(allowed[i] for i in range(7) if mask>>i&1)))>=mask.bit_count() for mask in range(1,128))
 good=0;tested=0
 # Choose the single host, not the author's double-host-pair Cartesian product.
 for singles in itertools.product(*unused):
  tested+=1;pairs=[tuple(x for x in U if x!=single) for U,single in zip(unused,singles)]
  predicted=len(set(pairs))==7 and all(pair in allowed[i] for i,pair in enumerate(pairs))
  # Different vertex numbering: H0..6,E7..13,D14..20,L21..27,P28..48.
  g=[set() for _ in range(49)]
  def edge(u,v):g[u].add(v);g[v].add(u)
  for i in range(7):
   edge(i,14+i);edge(i,21+i);edge(21+i,7+singles[i])
   for x in pairs[i]:edge(14+i,7+x)
  for k,(i,j) in enumerate(K):
   edge(i,28+k);edge(j,28+k)
   if (i,j) in phi:edge(28+k,7+phi[i,j])
  for u,v in F:edge(7+u,7+v)
  assert all(len(g[i])==8 for i in range(7)) and all(len(g[x])==7 for x in range(7,14))
  # Count unordered length-two paths by endpoints instead of intersecting neighbour sets.
  common=collections.Counter(pair for ns in g for pair in itertools.combinations(sorted(ns),2))
  assert all(common[i,x]==1 for i in range(7) for x in range(7,14))
  actual=max(common.values())<=1
  assert actual==predicted
  good+=actual
 assert good==r['c4_free_choices']==r['matching_count'] and hall==(good>0)
 out.append({'R':r['R_case'],'F':r['F_case'],'tested':tested,'good':good,'Hall_condition':hall})
r={'status':'PASS','fixtures':out,'total_direct_graph_checks':sum(x['tested'] for x in out),'pins':pins,'seconds':time.monotonic()-start,'scope':'Independent opposite-single-host enumeration, different49vertex numbering, length-two path collision counts, Hall-subset existence check. Fixed colouring fixtures only, no R/F-class or full H7 exclusion.'}
(O/'results.json').write_text(json.dumps(r,indent=2)+'\n');print({k:v for k,v in r.items() if k!='pins'})
