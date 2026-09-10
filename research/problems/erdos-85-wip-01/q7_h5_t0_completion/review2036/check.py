import itertools,json,hashlib
from pathlib import Path
source=Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3/t0-final-capacity');pins=json.loads((source/'PINS.json').read_text())
for n,h in pins.items():assert hashlib.sha256((source/n).read_bytes()).hexdigest()==h
S=list(map(set,itertools.combinations(range(5),2)));cycles=[[0,2,7,8,6],[1,3,9,5,4]];E=set()
for cycle in cycles:
 for a,b in zip(cycle,cycle[1:]+cycle[:1]):E.add(tuple(sorted((a,b))))
mask=sum(1<<k for k,e in enumerate(itertools.combinations(range(10),2)) if e in E);assert mask==5774048758818
core_path=source.parent/'t0-empty-completion/core-t0.json';raw=core_path.read_bytes();c=json.loads(raw);assert mask in c['canonical_cores'];assert c['masks']==[sum(1<<v for v in s) for s in S]
g=[set() for _ in range(15)]
for i,s in enumerate(S):
 for h in s:g[h].add(5+i);g[5+i].add(h)
for a,b in E:g[5+a].add(5+b);g[5+b].add(5+a)
assert all(len(g[a]&g[b])<=1 for a,b in itertools.combinations(range(15),2))
needed=[]
for v in range(5,15):
 heavy=g[v]&set(range(5,15));assert len(heavy)==2
 counts=[sum(h in g[w] for w in heavy) for h in range(5)];assert sorted(counts)==[0,1,1,1,1]
 singleton_required=counts.count(0);needed.append(7-len(g[v])-singleton_required)
pairs=[(a-5,b-5) for a,b in itertools.combinations(range(5,15),2) if not g[a]&g[b]]
assert pairs==[(0,9),(1,6),(2,4),(3,7),(5,8)]
assert needed==[2]*10;assert sum(needed)>14+len(pairs)
r={'status':'PASS','core':mask,'source_sha256':hashlib.sha256(raw).hexdigest(),'pins_verified':pins,'method':'Construct two explicit cycles and full15vertex support graph independently; encode cycle edges back to source core; common-neighbour checks use full graph rather than separate support/adjacency predicates.','compatible_pairs':pairs,'required_incidence':sum(needed),'upper_bound':14+len(pairs),'proof':'BC=J forces one singleton neighbour for each heavy, leaving two empty neighbours. An empty can host at most two size2 supports, and double-host pairs inject into five eligible pairs by C4-freeness. Thus20<=14+5=19, contradiction.','scope':'All completions of this one heavy core excluded under reviewed T0 premises; no search replay, no kernel/globalT0 claim.'}
Path(__file__).with_name('review-result.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r))
