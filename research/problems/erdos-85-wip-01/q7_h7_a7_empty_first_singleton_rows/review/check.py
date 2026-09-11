from pathlib import Path
import json,gzip,itertools,hashlib,time,collections
p=Path('/Users/rwalters/lean-genius-q7-outside-first-20260910/h7-a7-empty-first-singleton-rows');o=Path(__file__).parent;pins=json.loads((p/'pins.json').read_text());assert all(hashlib.sha256((p/f).read_bytes()).hexdigest()==h for f,h in pins.items())
data=json.loads(gzip.decompress((p/'results.json.gz').read_bytes()));records=data['results'];normal=json.loads((p/'normal-form-source.json').read_text());assert len(records)==117
K=list(itertools.combinations(range(7),2));Fs=[{tuple(sorted((i,(i+1)%7))) for i in range(7)},{(0,1),(0,2),(1,2),(3,4),(3,5),(4,5),(5,6)}];expected=set()
for fi,f in enumerate(normal['fixtures']):
 fg=[set() for _ in range(7)]
 for a,b in Fs[f['F_case']]:fg[a].add(b);fg[b].add(a)
 for singles in itertools.product(*f['unused']):
  pairs=tuple(tuple(sorted(set(U)-{v})) for U,v in zip(f['unused'],singles))
  if len(set(pairs))==7 and all(not fg[a]&fg[b] for a,b in pairs):expected.add((fi,pairs))
assert len(expected)==117 and expected=={(r['fixture_index'],tuple(map(tuple,r['choices']))) for r in records}
rows=failures=0;start=time.monotonic();arc_indices=[]
for index,r in enumerate(records):
 f=normal['fixtures'][r['fixture_index']];phi={tuple(e):x for e,x in f['phi']};g=[set() for _ in range(49)]
 def add(u,v):g[u].add(v);g[v].add(u)
 for i in range(7):
  for v in [7+2*i,8+2*i]:add(i,v)
  for x in r['choices'][i]:add(7+2*i,42+x)
  add(8+2*i,42+next(iter(set(f['unused'][i])-set(r['choices'][i]))))
 for k,(a,b) in enumerate(K):
  add(a,21+k);add(b,21+k)
  if (a,b) in phi:add(21+k,42+phi[a,b])
 for a,b in Fs[f['F_case']]:add(42+a,42+b)
 assert [sorted(ns) for ns in g]==r['adjacency']
 domains={}
 for u in range(7,21):
  need=5-2*len(g[u]&set(range(42,49)));answers=set()
  for selected in itertools.combinations([v for v in range(7,21) if u!=v and not g[u]&g[v]&set(range(7))],need):
   ns=g[u]|set(selected)
   if all(not((g[v]-{u})&(g[w]-{u})) for v,w in itertools.combinations(ns,2)):answers.add(frozenset(selected))
  assert len(r['initial'][str(u)])==len(answers) and answers==set(map(frozenset,r['initial'][str(u)]));domains[u]=answers;rows+=len(answers)
 for e in r['events']:
  u,v=e['vertex'],e['against'];removed=set(map(frozenset,e['removed']));assert u!=v and len(removed)==len(e['removed']) and removed<=domains[u]
  for a in removed:
   for b in domains[v]:assert ((v in a)!=(u in b)) or len((g[u]|a)&(g[v]|b))>1;failures+=1
  domains[u]-=removed
 if r['status']=='ARC_NEGATIVE':assert not domains[r['vertex']]
 else:
  assert r['status']=='ARC_CONSISTENT' and domains=={int(u):set(map(frozenset,v)) for u,v in r['remaining'].items()};arc_indices.append(index)
assert len(arc_indices)==25
completion=json.loads((p/'completion-results.json').read_text())['results'];assert [r['source_index'] for r in completion]==arc_indices
# Independently finalize vertices in descending fixed order, never row products
# or the author's most-constrained whole-star order.
answers_by_index={};nodecounts={};deadline=time.monotonic()+60
for entry in completion:
 index=entry['source_index'];g=list(map(set,records[index]['adjacency']));V=set(range(7,21));target={u:5-2*len(g[u]&set(range(42,49))) for u in V};answers=set();nodes=0
 def tick():
  global nodes
  nodes+=1
  if nodes>100000 or time.monotonic()>deadline:raise TimeoutError
 def visit(u):
  tick()
  if u<7:
   assert all(len(g[v]&V)==target[v] for v in V);answers.add(tuple((a,b) for a in sorted(V) for b in sorted(g[a]&V) if a<b));return
  need=target[u]-len(g[u]&V)
  if need<0:return
  choices=[v for v in range(7,u) if v not in g[u] and len(g[v]&V)<target[v] and not(g[u]&g[v]&set(range(7)))]
  for selected in itertools.combinations(choices,need):
   tick()
   for v in selected:g[u].add(v);g[v].add(u)
   if all(len(g[a]&g[b])<=1 for a in range(49) for b in range(a)):visit(u-1)
   for v in selected:g[u].remove(v);g[v].remove(u)
 visit(20);assert entry['status']=='COMPLETE' and answers=={tuple(map(tuple,x)) for x in entry['solutions']}
 answers_by_index[index]=answers;nodecounts[index]=nodes
surviving=json.loads((p/'surviving-bases.json').read_text());indices={i for i,a in answers_by_index.items() if a};assert len(indices)==18 and {r['source_index'] for r in surviving}==indices and len(surviving)==18
assert all(r['adjacency']==records[r['source_index']]['adjacency'] for r in surviving)
assert all(hashlib.sha256((p/f).read_bytes()).hexdigest()==h for f,h in pins.items())
out={'status':'PASS','fixed_partials':117,'initial_rows':rows,'failed_supports':failures,'arc_negative':92,'completed_cases':25,'additional_negative':sum(not a for a in answers_by_index.values()),'surviving_bases':18,'singleton_solutions':sum(map(len,answers_by_index.values())),'fixed_vertex_nodes':nodecounts,'seconds':time.monotonic()-start,'pins':pins,'scope':'Only two fixed proper-colouring witnesses and their117partial graphs; no fullcolouring/R-F/a7/H7 exclusion.'};(o/'results.json').write_text(json.dumps(out,indent=2)+'\n');print({k:v for k,v in out.items() if k not in ['fixed_vertex_nodes','pins']})
