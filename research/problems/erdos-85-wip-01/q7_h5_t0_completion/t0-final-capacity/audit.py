import itertools,json,hashlib
from pathlib import Path
p=Path(__file__).parent
source=p.parent/'t0-empty-completion/core-t0.json';raw=source.read_bytes();C=json.loads(raw);masks=C['masks'];core=5774048758818;assert core in C['canonical_cores']
H=[set() for _ in masks];edges=[]
for i,(u,v) in enumerate(itertools.combinations(range(10),2)):
 if core>>i&1:H[u].add(v);H[v].add(u);edges.append((u,v))
assert all(len(s)==2 for s in H)
missing=[]
for v in range(10):
 covered=[c for w in H[v] for c in range(5) if masks[w]>>c&1]
 assert len(covered)==len(set(covered))==4
 missing.append(next(c for c in range(5) if c not in covered))
compatible=[(u,v) for u,v in itertools.combinations(range(10),2) if not masks[u]&masks[v] and not H[u]&H[v]]
assert compatible==[(0,9),(1,6),(2,4),(3,7),(5,8)]
# Every heavy has 2 high, 2 heavy, 1 singleton neighbors, hence 2 empty.
heavy_empty=10*(7-2-2-1);empty_count=49-5-10-20
max_incidence=empty_count+len(compatible)
assert heavy_empty==20 and empty_count==14 and max_incidence==19
out=dict(core=core,source_sha256=hashlib.sha256(raw).hexdigest(),heavy_edges=edges,missing_singleton_colours=missing,compatible_heavy_pairs=compatible,required_heavy_empty_incidence=heavy_empty,available_heavy_empty_incidence_upper_bound=max_incidence,scope='Finite exact core audit plus necessary incidence inequality; independent review pending; no capped search rerun')
(p/'result.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
