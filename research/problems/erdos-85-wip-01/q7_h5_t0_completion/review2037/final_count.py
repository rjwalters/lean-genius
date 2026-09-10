import json,pathlib,itertools
P=pathlib.Path('q7_h5_t0_completion');core=5774048758818;data=json.loads((P/'t0-singleton-pilot/core-t0.json').read_text());masks=[(1<<a)|(1<<b) for a,b in itertools.combinations(range(5),2)];assert data['masks']==masks and core in data['canonical_cores'];G=[set() for _ in masks]
for i,(u,v) in enumerate(itertools.combinations(range(10),2)):
 if core>>i&1:G[u].add(v);G[v].add(u)
assert all(len(ns)==2 for ns in G)
for ns in G:
 a,b=ns;assert masks[a]&masks[b]==0 and (masks[a]|masks[b]).bit_count()==4
eligible=[(a,b) for a,b in itertools.combinations(range(10),2) if masks[a]&masks[b]==0 and not(G[a]&G[b])];assert len(eligible)==5
required=sum(7-2-len(ns)-1 for ns in G);upper=14+len(eligible);assert required==20 and upper==19 and required>upper
result=dict(core=core,eligible_pairs=eligible,required_incidence=required,upper_bound=upper,scope='BC=J forces one singleton and two empty neighbours per heavy. Each empty has at most two heavy guests; each compatible pair appears at most once. Excludes all completions, without retrying capped search.')
pathlib.Path('counting-audit.json').write_text(json.dumps(result,indent=2)+'\n');print(result)
