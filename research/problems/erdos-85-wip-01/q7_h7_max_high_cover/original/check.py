from pathlib import Path
import json,itertools,math,hashlib,collections
p=Path(__file__).parent;src=Path('/tmp/erdos85-sol1-h7-host-profiles/results.json');d=json.loads(src.read_text())['results'];rows=[]
for a in [6,7,8,9]:
 bound=7-math.ceil(4*a/7);keys=[]
 for family in d:
  for i,profile in enumerate(family['representatives']):
   if sum(profile['empty_counts'][:2])<=bound:keys.append([family['twins_adjacent'],i])
 assert len(keys)=={6:16,7:16,8:9,9:2}[a]
 rows.append(dict(empty_edges=a,max_high_min_degree=7-bound,singleton_empty_sum_at_high0_max=bound,profile_keys=keys))
assert rows[-1]['profile_keys']==[[True,6],[False,14]]
# For a9, Q is K7 minus3 edges; inspect every possible missing-edge set.
edges=list(itertools.combinations(range(7),2));hist=collections.Counter()
for removed in itertools.combinations(edges,3):
 touched=set(itertools.chain.from_iterable(removed));universal=7-len(touched);assert universal>=1;hist[universal]+=1
assert sum(hist.values())==1330
out=dict(status='PASS',cases=rows,a9_complement_graphs=1330,a9_universal_vertex_histogram=dict(hist),source_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),scope='Choice-of-high0 cover, not exclusion of discarded nonmax representations. Conditional a9 closure requires both twin6 andcrossed14 excluded; no such combined exclusion asserted here.')
(p/'results.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
