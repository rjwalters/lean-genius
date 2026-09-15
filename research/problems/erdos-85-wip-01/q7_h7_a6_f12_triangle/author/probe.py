"""One triangle-obstruction probe on the exact unfinished F12 complement.
No row-domain generation, ARC, or rerun of the capped residual API.
"""
import gzip,hashlib,itertools,json,time
from pathlib import Path
P=Path(__file__).parent
R=Path('/Users/rwalters/GitHub/lean-genius/.codex/worktrees/erdos85-sol2-integration/research/problems/erdos-85-wip-01')
S=R/'q7_h7_a6_f12_host/original';F=R/'q7_h7_a6_f12_residual_frontier/original'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert not (P/'results.json').exists()
for base,manifest in [(S,'pins.json'),(F,'final-pins.json')]:
 for n,h in json.loads((base/manifest).read_text()).items():assert sha(base/n)==h,n
all_leaves=json.loads((F/'input-survivors.json').read_text());old=json.loads((F/'results.json').read_text())
assert all_leaves==json.loads((S/'survivors.json').read_text()) and len(all_leaves)==397234
assert old['visited']==395764 and old['retained']==[[227088,0,'UNKNOWN']]
unfinished=[[227088,0]]+all_leaves[old['visited']:]
assert len(unfinished)==1471 and len(set(map(tuple,unfinished)))==1471
wanted={gid for gid,j in unfinished}
bases={r['global_index']:[sum(1<<v for v in ns) for ns in r['neighbors']] for r in map(json.loads,gzip.open(S/'inputs.jsonl.gz','rt')) if r['global_index'] in wanted}
hosts={}
for name in json.loads((S/'results.json').read_text())['shards']:
 for r in map(json.loads,gzip.open(S/name,'rt')):
  if r['global_index'] in wanted:
   assert r['receipt']['status']=='COMPLETE';hosts[r['global_index']]=r['receipt']['solutions']
(P/'launch.json').write_text(json.dumps({'seconds':60,'cases':1471,'criterion':'pair_degree_two_requires_singleton_triangle','source_pins':sha(S/'pins.json'),'frontier_pins':sha(F/'final-pins.json'),'driver':sha(Path(__file__))},indent=2)+'\n')
start=time.monotonic();killed=[];remaining=[]
for gid,j in unfinished:
 assert time.monotonic()-start<60
 g=bases[gid][:]
 for e,m in enumerate(hosts[gid][j],42):
  g[e]|=m
  for v in range(49):
   if m>>v&1:g[v]|=1<<e
 cert=None
 for u in range(21,42):
  if g[u].bit_count()!=2:continue
  assert g[u]&127==g[u]
  cand=[v for v in range(7,21) if all(not(g[v]&g[w]) for w in range(49) if g[u]>>w&1)]
  compat={v:[w for w in cand if w!=v and not(g[v]&g[w])] for v in cand}
  triangles=[list(t) for t in itertools.combinations(cand,3) if all(b in compat[a] for a,b in itertools.combinations(t,2))]
  if not triangles:
   cert={'global_index':gid,'leaf_index':j,'vertex':u,'singleton_candidates':cand,'compatibility_edges':[[a,b] for a,b in itertools.combinations(cand,2) if b in compat[a]]};break
 if cert:killed.append(cert)
 else:remaining.append([gid,j])
result={'status':'COMPLETE_PROBE','total':1471,'killed':len(killed),'remaining':remaining,'certificates':killed,'seconds':time.monotonic()-start,'scope':'New necessary triangle criterion only. Old capped receipt unchanged; absence of this obstruction is not feasibility.'}
(P/'results.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k not in ['certificates','remaining']}));print('remaining',len(remaining))
