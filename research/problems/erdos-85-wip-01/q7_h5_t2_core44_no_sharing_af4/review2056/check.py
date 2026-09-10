import itertools,json
from pathlib import Path
p=Path(__file__).parent
sources=['f0','f1','f2','f3','f4'];targets=['a0','b0','p','q','r'];names=sources+targets+['F'];idx={v:i for i,v in enumerate(names)};cases=[]
for ts in itertools.permutations(targets):
 assignment=dict(zip(sources,ts))
 if assignment['f0']!='p' or assignment['f4']!='a0' or assignment['f2']!='b0':continue
 g=[set() for _ in names]
 for a,b in [('F',v) for v in sources]+[('f1','f3'),('q','r')]+list(assignment.items()):
  g[idx[a]].add(idx[b]);g[idx[b]].add(idx[a])
 bad=[dict(vertices=[names[a],names[b]],common=[names[v] for v in sorted(g[a]&g[b])]) for a,b in itertools.combinations(range(len(names)),2) if len(g[a]&g[b])>1]
 assert bad
 cycle=['f1','f3',assignment['f3'],assignment['f1']]
 assert len(set(cycle))==4 and all(idx[b] in g[idx[a]] for a,b in zip(cycle,cycle[1:]+cycle[:1]))
 cases.append(dict(assignment=assignment,cycle=cycle))
assert len(cases)==2
out=dict(bijections_examined=120,compatible_target_assignments=2,c4_free_assignments=0,cases=cases,scope='No-sharing af4/bf2 exclusion under reviewed F-star saturation and elementary S0 matching; no completion search, no Lean theorem.')
(p/'results.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
