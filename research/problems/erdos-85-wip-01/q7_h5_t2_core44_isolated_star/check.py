from pathlib import Path
import itertools,json
S=[{0,1,2},{0,3,4},{1,3},{1,4},{2,3},{2,4}];edges=[e for i,e in enumerate(itertools.combinations(range(6),2)) if 44>>i&1];N=[set() for _ in S]
for a,b in edges:N[a].add(b);N[b].add(a)
assert not N[5];dem=[2-len(S[v])+sum(len(S[w])-1 for w in N[v]) for v in range(6)];assert dem[5]==0
compatible=[v for v in range(5) if not S[v]&S[5]];assert compatible==[2]
Cmissing=set(range(5))-set().union(*(S[v] for v in N[2]));assert Cmissing=={1,2}
profiles=[]
for shared in [None,1,2]:
 ds=[3 if c==shared else 2 for c in range(5)];profiles.append({'C_F_shared_singleton_colour':shared,'F_singleton_empty_degrees':ds,'covered_empties':sum(ds),'uncovered_empties':12-sum(ds)})
r={'core':44,'edges':edges,'heavy_empty_demands':dem,'possible_second_heavy_for_F_singleton':compatible,'C_uncovered_colours':sorted(Cmissing),'profiles':profiles,'scope':'Necessary isolated-F star partition. Pairwise disjoint empty sets follow from commonF and C4. No exclusion or search.'};Path(__file__).with_name('results.json').write_text(json.dumps(r,indent=2)+'\n');print(r)
