import pathlib,json,itertools,hashlib,sqlite3
from joint_function import feasible
ROOT=pathlib.Path('/Users/rwalters/GitHub/lean-genius/.codex/worktrees/erdos85-sol2-integration/research/problems/erdos-85-wip-01');H=ROOT/'q7_h5_heavy_core';T=ROOT/'q7_h5_t1_heavy_core';E=ROOT/'q7_h5_t1_empty_pilot'
base=json.loads((H/'core-t1.json').read_text());masks=base['masks'];pairs=list(itertools.combinations(range(8),2));pairid={p:i for i,p in enumerate(pairs)};transforms=[]
for p in itertools.permutations(range(5)):
 def image(m):return sum(1<<p[c] for c in range(5) if m>>c&1)
 if image(7)!=7:continue
 perm=[masks.index(image(m)) for m in masks];transforms.append([1<<pairid[tuple(sorted((perm[u],perm[v])))] for u,v in pairs])
def canonical(edges):return min(sum(t[pairid[tuple(edge)]] for edge in edges) for t in transforms)
source=json.loads((T/'results.json').read_text());joint=json.loads((T/'joint-results.json').read_text());first=json.loads((T/'singleton-results.json').read_text());tail=json.loads((T/'singleton-tail-results.json').read_text());last=json.loads((E/'singleton-empty-results.json').read_text())
all_author=source['survivors']+source['rejections'];canon=[canonical(r['edges']) for r in all_author];assert len(canon)==len(set(canon))==249 and set(canon)==set(base['canonical_cores'])
independent=set()
for core in base['canonical_cores']:
 adj=[set() for _ in masks]
 for i,(u,v) in enumerate(pairs):
  if core>>i&1:adj[u].add(v);adj[v].add(u)
 if feasible(masks,adj,[5,5,5,4,4]):independent.add(core)
claimed={canonical(source['survivors'][r['core_index']]['edges']) for r in joint['rows'] if r['status']=='PASS'};assert independent==claimed and len(independent)==211
rows=first['rows']+tail['rows'];assert len(rows)==211 and len({r['core_index'] for r in rows})==211
assert {canonical(source['survivors'][r['core_index']]['edges']) for r in rows}==independent
remaining={r['core_index'] for r in rows if r['status']=='PASS'};assert len(remaining)==10 and remaining=={r['core_index'] for r in last['rows']}
assert all(r['status']=='REJECT' for r in last['rows'])
review=json.loads(pathlib.Path('singleton-rejection-audit.json').read_text());assert remaining=={r['core'] for r in review['results']} and all(r['status']=='INDEPENDENTLY_EXHAUSTED' for r in review['results'])
for path in [T/'singleton-pins.json',T/'singleton-tail-pins.json',E/'exhaustive-pins.json']:
 for n,h in json.loads(path.read_text()).items():assert hashlib.sha256((path.parent/n).read_bytes()).hexdigest()==h
replay=json.loads(pathlib.Path('author-replay/singleton-empty-results.json').read_text());assert replay['rows']==last['rows'] and replay['counts']==last['counts']
result=dict(heavy_domain=249,joint_feasible=211,singleton_exhausted=201,remaining_empty_exhausted=10,remaining=0,independent_joint_exact_set=True,disjoint_complete_chain=True,author_replay_identical_rows=True,scope='Conditional on reviewed H5/T1 support census and block identities: finite-computation exclusion of T1, not a Lean theorem or global H5 exclusion.')
pathlib.Path('chain-audit.json').write_text(json.dumps(result,indent=2)+'\n');print(result)
