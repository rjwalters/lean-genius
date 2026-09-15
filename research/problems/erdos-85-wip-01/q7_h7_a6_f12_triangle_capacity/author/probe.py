"""Triangle-conditioned colour matching obstruction; no residual row/ARC API."""
import gzip,hashlib,itertools,json,sqlite3,time
from pathlib import Path
D=Path(__file__).parent;T=Path('/Users/rwalters/lean-genius-h7-a6-f12-support-capacity-sol2-20260915')
R=Path('/Users/rwalters/GitHub/lean-genius/.codex/worktrees/erdos85-sol2-integration/research/problems/erdos-85-wip-01');S=R/'q7_h7_a6_f12_host/original'
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert not (D/'launch.json').exists()
db=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True)
st,res=db.execute('select status,resolution from review_requests where id=2705').fetchone();assert st=='resolved' and res.startswith('PASS')
for base in [T,S]:
 for n,h in read(base/'pins.json').items():assert sha(base/n)==h,n
cases=read(T/'results.json')['remaining'];assert len(cases)==218
ids={gid for gid,j in cases}
bases={r['global_index']:[sum(1<<v for v in ns) for ns in r['neighbors']] for r in map(json.loads,gzip.open(S/'inputs.jsonl.gz','rt')) if r['global_index'] in ids}
hosts={}
for name in read(S/'results.json')['shards']:
 for r in map(json.loads,gzip.open(S/name,'rt')):
  if r['global_index'] in ids:hosts[r['global_index']]=r['receipt']['solutions']
(D/'launch.json').write_text(json.dumps({'seconds':60,'cases':218,'source_manifest':sha(T/'pins.json'),'host_manifest':sha(S/'pins.json'),'driver':sha(Path(__file__)),'review2705':res},indent=2)+'\n')
start=time.monotonic();certs=[];remaining=[]
for gid,j in cases:
 assert time.monotonic()-start<60
 g=bases[gid][:]
 for e,m in enumerate(hosts[gid][j],42):
  g[e]|=m
  for v in range(49):
   if m>>v&1:g[v]|=1<<e
 chosen_certificate=None
 for u in range(21,42):
  if g[u].bit_count()!=2:continue
  assert g[u]&127==g[u]
  old=[w for w in range(7) if g[u]>>w&1]
  candidates=[s for s in range(7,21) if all(not(g[s]&g[w]) for w in old)]
  triangles=[t for t in itertools.combinations(candidates,3) if all(not(g[a]&g[b]) for a,b in itertools.combinations(t,2))]
  assert triangles,'Prior triangle criterion should exclude this input'
  cuts=[]
  for tri in triangles:
   used=0
   for s in tri:used|=g[s]&127
   assert used.bit_count()==3
   left=127^used
   pairs=[p for p in range(21,42) if p!=u and not((g[p]&127)&~left) and all(not(g[p]&g[w]) for w in old+list(tri))]
   # A matching in high-colour supports is necessary. Ignore pair-pair geometry.
   if any(not((g[a]&127)&(g[b]&127)) for a,b in itertools.combinations(pairs,2)):break
   cuts.append({'triangle':list(tri),'remaining_colours':left,'pair_candidates':pairs})
  if len(cuts)==len(triangles):chosen_certificate={'global_index':gid,'leaf_index':j,'vertex':u,'cuts':cuts};break
 if chosen_certificate:certs.append(chosen_certificate)
 else:remaining.append([gid,j])
out={'status':'COMPLETE_PROBE','total':218,'killed':len(certs),'certificates':certs,'remaining':remaining,'seconds':time.monotonic()-start,'scope':'Triangle-conditioned high-colour matching obstruction only; no full residual row generation or ARC. Unclassified cases preserved.'}
(D/'results.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k not in ['certificates','remaining']}));print('remaining',len(remaining))
