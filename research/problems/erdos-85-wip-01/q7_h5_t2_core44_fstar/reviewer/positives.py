from pathlib import Path
import json,itertools,hashlib
s=Path('/Users/rwalters/lean-genius-q7-outside-first-20260910/core44-special-projection');pins=json.loads((s/'fstar-pins.json').read_text())
for n,h in pins.items():assert hashlib.sha256((s/n).read_bytes()).hexdigest()==h
base={r['omitted']:r for r in json.loads((s/'four-pattern-results.json').read_text())['results']};rows=json.loads((s/'fstar-empty-results.json').read_text())['results'];verified=[];neg=[]
assert len(rows)==4
for row in rows:
 assert {(x['af'],x['bf']) for x in row['choices']}==set(itertools.product([3,4],[1,2]))
 for x in row['choices']:
  if x['status']=='EXHAUSTED':neg.append([row['omitted'],x['af'],x['bf']]);continue
  assert x['status']=='PARTIAL_WITNESS';g=list(map(set,x['adjacency']));assert len(g)==32
  assert all(a!=b and a in g[b] for a in range(32) for b in g[a])
  assert all(set(ns)<=g[v] for v,ns in enumerate(base[row['omitted']]['skeleton']))
  assert all(len(g[a]&g[b])<=1 for a,b in itertools.combinations(range(32),2))
  assert 30 in g[28] and 27+x['af'] in g[23] and 27+x['bf'] in g[24]
  for c in range(5):
   v=27+c;assert g[v]&set(range(5))=={c};assert g[v]&set(range(5,11))=={10};assert len(g[v]&set(range(11,23)))==2
  for e in range(11,23):assert len(g[e]&set(range(11,23)))==2+sum(len(g[h]&set(range(5)))-1 for h in g[e] if 5<=h<11)
  verified.append([row['omitted'],x['af'],x['bf']])
assert len(verified)==14 and sorted(neg)==[[0,3,1],[11,3,1]]
r={'status':'PASS','verified_partials':verified,'exact_negative_branches':neg,'pins':pins,'scope':'16case partition and14partial witnesses only; negative exhaustion verified separately, no full-core exclusion.'};Path(__file__).with_name('positive-results.json').write_text(json.dumps(r,indent=2)+'\n');print(len(verified))
