from pathlib import Path
import itertools,json,hashlib
src=Path('/Users/rwalters/lean-genius-q7-outside-first-20260910/t2-integrated-empty');pins=json.loads((src/'source-pins.json').read_text())
for n,h in pins.items():
 p=Path(n);p=p if p.is_absolute() else src/p;assert hashlib.sha256(p.read_bytes()).hexdigest()==h
pairs=list(itertools.combinations(range(5),2));checks=0
for bits in range(1<<len(pairs)):
 g=[set() for _ in range(5)]
 for i,(a,b) in enumerate(pairs):
  if bits>>i&1:g[a].add(b);g[b].add(a)
 old={p for p in pairs if g[p[0]]&g[p[1]]}
 for u,v in pairs:
  if v in g[u]:continue
  predicted=old|{tuple(sorted((v,w))) for w in g[u]}|{tuple(sorted((u,w))) for w in g[v]}
  g[u].add(v);g[v].add(u)
  actual={p for p in pairs if g[p[0]]&g[p[1]]};assert predicted==actual
  g[u].remove(v);g[v].remove(u);checks+=1
out={'pins_verified':pins,'edge_insertion_checks':checks,'graphs':1024,'status':'PASS','scope':'Exact newly-common-neighbour update checked on every simple5vertex graph and absent edge. General proof follows from new length2paths using the inserted edge; does not replace core completeness audit.'}
Path(__file__).with_name('boundary-result.json').write_text(json.dumps(out,indent=2)+'\n');print(checks)
