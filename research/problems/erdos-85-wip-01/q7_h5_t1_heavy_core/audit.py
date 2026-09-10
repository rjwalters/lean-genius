"""Audit retained T1 representatives as explicit 13-vertex partial graphs."""
import json,itertools,hashlib
from pathlib import Path
p=Path(__file__).parent;raw=(p/'results.json').read_bytes();r=json.loads(raw);supports=[set(s) for s in r['supports']];by={frozenset(s):i for i,s in enumerate(supports)};seen=set();totals={'survivors':0,'rejections':0}
for status in totals:
 for row in r[status]:
  key=tuple(tuple(e) for e in row['edges']);assert key not in seen;seen.add(key)
  adjacency=[set() for _ in range(13)]
  for i,s in enumerate(supports):
   for c in s:adjacency[c].add(5+i);adjacency[5+i].add(c)
  for i,j in key:adjacency[5+i].add(5+j);adjacency[5+j].add(5+i)
  assert all(len(adjacency[i]&adjacency[j])<=1 for i,j in itertools.combinations(range(13),2))
  images=set()
  for a in itertools.permutations(range(3)):
   for b in itertools.permutations((3,4)):
    colour=a+b;perm=[by[frozenset(colour[c] for c in s)] for s in supports]
    images.add(tuple(sorted(tuple(sorted((perm[i],perm[j]))) for i,j in key)))
  assert min(images)==key;assert len(images)==row['labelled_count'];totals[status]+=len(images)
assert totals=={'survivors':2440,'rejections':138};assert len(seen)==249
out={'source_results_sha256':hashlib.sha256(raw).hexdigest(),'representatives_checked':len(seen),'expanded_orbit_counts':totals,'all_explicit_partial_graphs_c4_free':True,'scope':'Independent representation/orbit-size check, not a second exhaustive census or full graph completion.'};(p/'audit-results.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
