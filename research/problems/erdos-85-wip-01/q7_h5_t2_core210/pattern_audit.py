import pathlib,json,itertools,hashlib
P=pathlib.Path(__file__).parent;rows=json.loads((P/'core210-pattern.json').read_text());assert len(rows)==1;r=rows[0];assert r['core']==210
masks=[7,25,10,18,12,20];G=[set() for _ in masks]
for i,(u,v) in enumerate(itertools.combinations(range(6),2)):
 if 210>>i&1:G[u].add(v);G[v].add(u)
demand=[2-masks[u].bit_count()+sum(masks[v].bit_count()-1 for v in G[u]) for u in range(6)]
assert demand==r['heavy_empty_demands']==[1,1,2,2,2,2]
compatible=[(u,v) for u,v in itertools.combinations(range(6),2) if not(masks[u]&masks[v]) and not(G[u]&G[v])];assert compatible==r['compatible_pairs']==[]
expected=[[u] for u in range(6) for _ in range(demand[u])]+[[],[]];assert len(r['patterns'])==1 and r['patterns'][0]['heavy_rows']==expected
assert r['patterns'][0]['empty_degrees']==[2+sum(masks[u].bit_count()-1 for u in row) for row in expected]
base=pathlib.Path('/Users/rwalters/GitHub/lean-genius/.codex/worktrees/erdos85-sol2-integration/research/problems/erdos-85-wip-01/q7_h5_heavy_core/core-t2.json');raw=base.read_bytes();data=json.loads(raw);assert data['masks']==masks and 210 in data['canonical_cores']
(P/'pattern-audit.json').write_text(json.dumps(dict(core=210,source_sha256=hashlib.sha256(raw).hexdigest(),heavy_empty_demands=demand,compatible_pairs=compatible,unique_pattern=True,empty_degrees=r['patterns'][0]['empty_degrees']),indent=2)+'\n')
print('Unique heavy-empty pattern verified')
