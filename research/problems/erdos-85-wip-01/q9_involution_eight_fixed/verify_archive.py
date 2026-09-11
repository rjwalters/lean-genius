"""Read-only archive audit; no capped discovery rerun or solver calls."""
from pathlib import Path
from itertools import combinations,combinations_with_replacement
import json,hashlib
p=Path(__file__).resolve().parent
read=lambda f:json.loads((p/f).read_text())
pins=read('payload-pins.json')
for f,h in pins.items():assert (p/f).resolve().is_relative_to(p) and hashlib.sha256((p/f).read_bytes()).hexdigest()==h,f
for rec in read('provenance.json'):
 directory=p/rec['archive_directory']
 for f,h in json.loads((directory/rec['pin_file']).read_text()).items():assert hashlib.sha256((directory/f).read_bytes()).hexdigest()==h,f
reviews=read('accepted-reviews.json');assert {r['id'] for r in reviews}=={2237,2239,2242}
assert all(r['status']=='resolved' and r['resolution'].startswith('PASS') for r in reviews)
for N in (78,80):
 r=read(f'q9-involution-n{N}-eight-fixed/results.json');assert r['status']=='COMPLETE'
 profiles={d for d in combinations_with_replacement((1,3,5,7),8) if sum(x*(x-1) for x in d)<=56 and all(x*(9-x)<=N-80+sum(d) for x in d)}
 assert profiles==set(map(tuple,r['degree_profiles'])) and len(profiles)==(5 if N==78 else 11)
 assert len(r['receipts'])==len(profiles) and all(a['status']=='COMPLETE' for a in r['receipts'])
 total=0
 for rec in r['receipts']:
  assert tuple(sorted(rec['degrees'])) in profiles
  seen=set()
  for graph in rec['solutions']:
   assert len(graph)==8;adj=list(map(set,graph));key=tuple(tuple(sorted(n)) for n in adj);assert key not in seen;seen.add(key)
   assert [len(n) for n in adj]==rec['degrees']
   assert all(i not in adj[i] and all(i in adj[j] for j in adj[i]) for i in range(8))
   assert all(len(adj[i]&adj[j])<=1 for i,j in combinations(range(8),2))
  total+=len(seen)
 assert total==(0 if N==78 else 106)
print(f'PASS: {len(pins)} payload hashes, six original manifests, three accepted reviews, five/eleven profiles, 106 positive fixed-subgraph witnesses.')
