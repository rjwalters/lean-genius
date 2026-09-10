import itertools,json
from pathlib import Path
S=[{0,1,2},{0,3,4},{1,3},{1,4},{2,3},{2,4}];H=[set() for _ in S]
for u,v in [(0,3),(0,4),(1,2)]:H[u].add(v);H[v].add(u)
assert sum(1<<i for i,e in enumerate(itertools.combinations(range(6),2)) if e[1] in H[e[0]])==44
assert not H[5] and [v for v in range(5) if not S[v]&S[5]]==[2]
missingC={c for c in range(5) if not any(c in S[w] for w in H[2])};assert missingC=={1,2}
profiles=[]
for share in [None,1,2]:
 counts=[]
 for colour in range(5):
  heavy=[5]+([2] if colour==share else []);w=sum(len(S[v]) for v in heavy);single=5-w;counts.append(7-1-len(heavy)-single)
 assert sum(counts) in [10,11];profiles.append(dict(shared=share,empty_degrees=counts))
valid=[];edges=list(itertools.combinations(range(5),2))
for mask in range(1024):
 G=[set() for _ in range(6)]
 for v in range(5):G[v].add(5);G[5].add(v)
 selected=[e for i,e in enumerate(edges) if mask>>i&1]
 for u,v in selected:G[u].add(v);G[v].add(u)
 if any(len(G[u]&G[v])>1 for u,v in itertools.combinations(range(6),2)):continue
 if any(v in [2,4] for edge in selected for v in edge):continue
 if not any(1 in e for e in selected) or not any(3 in e for e in selected):continue
 valid.append(selected)
assert valid==[[(1,3)]]
Path('independent-results.json').write_text(json.dumps(dict(profiles=profiles,all_internal_graphs_checked=1024,unique_internal_graph=valid[0],scope='Conditional no-sharing saturation checked independently; sharing branches remain separate'),indent=2)+'\n')
src=Path('/Users/rwalters/GitHub/lean-genius/.codex/worktrees/erdos85-sol2-integration/research/problems/erdos-85-wip-01/q7_h5_t2_core44_isolated_star')
for f in ['results.json','saturation-results.json']:assert Path(f).read_bytes()==(src/f).read_bytes()
print('Both replays exact; independent degree counts and1024internal graphs agree')
