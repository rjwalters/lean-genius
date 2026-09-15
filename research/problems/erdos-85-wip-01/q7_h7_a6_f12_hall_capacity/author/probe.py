"""One global capacitated Hall probe; no residual row or ARC API."""
import collections,gzip,hashlib,itertools,json,sqlite3,time
from pathlib import Path
D=Path(__file__).parent;T=Path('/Users/rwalters/lean-genius-h7-a6-f12-triangle-capacity-sol2-20260915')
R=Path('/Users/rwalters/GitHub/lean-genius/.codex/worktrees/erdos85-sol2-integration/research/problems/erdos-85-wip-01');S=R/'q7_h7_a6_f12_host/original'
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def eligibility(g):
 edges={};demand={p:7-2*g[p].bit_count() for p in range(21,42)};capacity={s:7-g[s].bit_count() for s in range(7,21)}
 assert set(demand.values())<={1,3} and set(capacity.values())<={2,3} and sum(demand.values())==sum(capacity.values())==39
 for p in range(21,42):
  old=[w for w in range(49) if g[p]>>w&1]
  candidates=[s for s in range(7,21) if all(not(g[s]&g[w]) for w in old)]
  if demand[p]==3:
   allowed=set()
   for tri in itertools.combinations(candidates,3):
    if any(g[a]&g[b] for a,b in itertools.combinations(tri,2)):continue
    used=0
    for s in tri:used|=g[s]&127
    assert used.bit_count()==3;left=127^used
    pairs=[q for q in range(21,42) if q!=p and not((g[q]&127)&~left) and all(not(g[q]&g[w]) for w in old+list(tri))]
    if any(not((g[a]&127)&(g[b]&127)) for a,b in itertools.combinations(pairs,2)):allowed.update(tri)
   candidates=sorted(allowed)
  edges[p]=candidates
 return edges,demand,capacity

def hall(edges,demand,capacity):
 source=0;sink=1;res=[[0]*42 for _ in range(42)]
 for p,n in demand.items():res[source][p]=n
 for p,ss in edges.items():
  for s in ss:res[p][s]=1
 for s,n in capacity.items():res[s][sink]=n
 flow=0
 while True:
  parent={source:None};q=collections.deque([source])
  while q and sink not in parent:
   u=q.popleft()
   for v,n in enumerate(res[u]):
    if n and v not in parent:parent[v]=u;q.append(v)
  if sink not in parent:break
  v=sink;amount=39
  while parent[v] is not None:u=parent[v];amount=min(amount,res[u][v]);v=u
  v=sink
  while parent[v] is not None:u=parent[v];res[u][v]-=amount;res[v][u]+=amount;v=u
  flow+=amount
 if flow==39:return None
 U=[p for p in demand if p in parent];lhs=sum(demand[p] for p in U);rhs=sum(min(capacity[s],sum(s in edges[p] for p in U)) for s in capacity)
 assert lhs>rhs
 return {'pair_subset':U,'demand':lhs,'capacity':rhs,'flow_value':flow}

def main():
 assert not (D/'launch.json').exists()
 db=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True);st,review=db.execute('select status,resolution from review_requests where id=2706').fetchone();assert st=='resolved' and review.startswith('PASS')
 for base in [T,S]:
  for n,h in read(base/'pins.json').items():assert sha(base/n)==h,n
 cases=read(T/'results.json')['remaining'];assert len(cases)==129;ids={gid for gid,j in cases}
 bases={r['global_index']:[sum(1<<v for v in ns) for ns in r['neighbors']] for r in map(json.loads,gzip.open(S/'inputs.jsonl.gz','rt')) if r['global_index'] in ids};hosts={}
 for name in read(S/'results.json')['shards']:
  for r in map(json.loads,gzip.open(S/name,'rt')):
   if r['global_index'] in ids:hosts[r['global_index']]=r['receipt']['solutions']
 (D/'launch.json').write_text(json.dumps({'seconds':60,'cases':129,'source_manifest':sha(T/'pins.json'),'host_manifest':sha(S/'pins.json'),'driver':sha(Path(__file__)),'review2706':review},indent=2)+'\n')
 start=time.monotonic();certs=[];remaining=[]
 for gid,j in cases:
  assert time.monotonic()-start<60
  g=bases[gid][:]
  for e,m in enumerate(hosts[gid][j],42):
   g[e]|=m
   for v in range(49):
    if m>>v&1:g[v]|=1<<e
  edges,demand,capacity=eligibility(g);cert=hall(edges,demand,capacity)
  if cert:cert.update(global_index=gid,leaf_index=j,eligible_edges=edges);certs.append(cert)
  else:remaining.append([gid,j])
 out={'status':'COMPLETE_PROBE','total':129,'killed':len(certs),'certificates':certs,'remaining':remaining,'seconds':time.monotonic()-start,'scope':'Global necessary singleton–pair Hall capacity only; no graph feasibility claim for survivors.'}
 (D/'results.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k not in ['certificates','remaining']}));print('remaining',len(remaining))
if __name__=='__main__':main()
