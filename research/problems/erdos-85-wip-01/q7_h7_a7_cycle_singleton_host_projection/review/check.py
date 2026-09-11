from pathlib import Path
import json,itertools,math,time,hashlib,collections
P=Path('/Users/rwalters/lean-genius-q7-outside-first-20260910/h7-a7-cycle-singleton-host-projection');O=Path(__file__).parent;sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();pins=json.loads((P/'pins.json').read_text())
for f,h in pins.items():assert sha(P/f)==h
cover=json.loads((P/'results.json').read_text());rows=json.loads((P/'row-results.json').read_text())['results'];done=json.loads((P/'completion-results.json').read_text())['results'];E=list(map(tuple,cover['allowed']));ei={e:i for i,e in enumerate(E)};assert len(E)==14
assert set(map(tuple,cover["F_edges"]))=={tuple(sorted((i,(i+1)%7))) for i in range(7)}
assert E==[e for e in itertools.combinations(range(7),2) if (e[1]-e[0])%7 in [1,3,4,6]]
raw=set()
for mask in range(1<<14):
 if mask.bit_count()!=7:continue
 deg=[sum((mask>>i&1) for i,e in enumerate(E) if x in e) for x in range(7)]
 if max(deg)<=3:raw.add(mask)
seen=set()
for r in cover['representatives']:
 orbit={sum(1<<ei[tuple(sorted(((t+s*x)%7,(t+s*y)%7)))] for x,y in r['edges']) for t in range(7) for s in [-1,1]}
 assert not seen&orbit and orbit<=raw and len(orbit)==r['orbit_size'];seen|=orbit
assert seen==raw and len(raw)==2606 and len(cover['representatives'])==202

def bits(mask):
 while mask:
  b=mask&-mask;yield b.bit_length()-1;mask-=b
start=time.monotonic();records=[];totalrows=0
for index,r in enumerate(cover['representatives']):
 base=[0]*21
 def edge(g,u,v):g[u]|=1<<v;g[v]|=1<<u
 for x,y in cover['F_edges']:edge(base,x,y)
 expected=[list(e) for e in r['edges']]
 for x in range(7):expected.extend([[x]]*(3-sum(x in e for e in r['edges'])))
 assert expected==r['singleton_hosts']
 for u,hosts in enumerate(expected,7):
  for x in hosts:edge(base,u,x)
 assert all((base[u]&base[v]).bit_count()<=1 for u in range(21) for v in range(u))
 target={u:5-base[u].bit_count() for u in range(7,21)}
 for u in range(7,21):
  actual=[]
  for chosen in itertools.combinations([v for v in range(7,21) if v!=u],target[u]-base[u].bit_count()):
   final=list(bits(base[u]))+list(chosen)
   if all(not (base[a]&base[b]&~(1<<u)) for a,b in itertools.combinations(final,2)):actual.append(list(chosen))
  assert actual==rows[index]['rows'][str(u)];totalrows+=len(actual)
 g=base[:];solutions=set();nodes=0
 def visit(unfixed):
  global nodes
  nodes+=1
  if nodes>100000 or time.monotonic()-start>60:raise TimeoutError
  if not unfixed:
   assert all(g[u].bit_count()==target[u] for u in target)
   assert all((g[u]&g[v]).bit_count()<=1 for u in range(21) for v in range(u))
   solutions.add(tuple((u,v) for u in range(7,21) for v in bits(g[u]) if v>u));return
  choices=[]
  for u in unfixed:
   need=target[u]-g[u].bit_count()
   if need<0:return
   candidates=[v for v in unfixed if v!=u and target[v]>g[v].bit_count() and not(g[u]>>v&1) and all(not(g[v]&g[w]) for w in bits(g[u]))]
   if need>len(candidates):return
   choices.append((math.comb(len(candidates),need),u,need,candidates))
  _,u,need,candidates=min(choices,key=lambda x:(x[0],-x[1]))
  for block in itertools.combinations(candidates,need):
   if any(g[v]&g[w] for v,w in itertools.combinations(block,2)):continue
   old=g[u]
   for v in block:edge(g,u,v)
   visit(tuple(v for v in unfixed if v!=u))
   for v in block:g[v]^=1<<u
   g[u]=old
 visit(tuple(range(7,21)))
 assert done[index]['status']=='COMPLETE'
 assert solutions=={tuple(map(tuple,s)) for s in done[index]['solutions']},index
 records.append({'index':index,'nodes':nodes,'solutions':len(solutions)})
for f,h in pins.items():assert sha(P/f)==h
r={'status':'PASS','cases':len(records),'raw_X':len(raw),'X_orbits':len(cover['representatives']),'rows':totalrows,'solutions':sum(r['solutions'] for r in records),'positive':sum(bool(r['solutions']) for r in records),'nodes':sum(r['nodes'] for r in records),'max_nodes':max(r['nodes'] for r in records),'seconds':time.monotonic()-start,'records':records,'pins':pins,'scope':'Independent direct graph MRV-star completion with incremental C4 edge/star tests; exactall202labelled solution sets. No high/Passignment or fullH7 exclusion.'};(O/'results.json').write_text(json.dumps(r,indent=2)+'\n');print({k:v for k,v in r.items() if k not in ['records','pins']})
