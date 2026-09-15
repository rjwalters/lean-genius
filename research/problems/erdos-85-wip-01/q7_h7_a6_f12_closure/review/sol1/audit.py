import gzip,hashlib,itertools,json,sqlite3,time
from pathlib import Path
P=Path('/Users/rwalters/lean-genius-h7-a6-f12-incidence-projection-sol2-20260915');T=Path('/Users/rwalters/lean-genius-h7-a6-f12-weighted-family-sol2-20260915');O=Path(__file__).parent
S=Path('/Users/rwalters/GitHub/lean-genius/.codex/worktrees/erdos85-sol2-integration/research/problems/erdos-85-wip-01/q7_h7_a6_f12_host/original')
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for d in [P,T,S]:
 for n,h in read(d/'pins.json').items():assert sha(d/n)==h
l=read(P/'launch.json');assert l['source_manifest']==sha(T/'pins.json') and l['host_manifest']==sha(S/'pins.json') and l['driver']==sha(P/'probe.py')
c=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True)
st,res=c.execute('select status,resolution from review_requests where id=2712').fetchone();assert st=='resolved' and res==l['review2712'] and res.startswith('PASS')
start=time.monotonic();out=read(P/'results.json');expected=set(map(tuple,read(T/'results.json')['remaining']));certs={(x['global_index'],x['leaf_index']):x for x in out['records']};rem=set(map(tuple,out['unvisited']))
assert len(expected)==23 and len(certs)==len(out['records'])==23 and not rem and set(certs)==expected
assert out['counts']=={'INFEASIBLE_PROJECTION':23,'FEASIBLE_PROJECTION':0,'UNKNOWN':0}
wanted={x for x,y in expected};inputs={}
for line in gzip.open(S/'inputs.jsonl.gz','rt'):
 r=json.loads(line)
 if r['global_index'] in wanted:inputs[r['global_index']]=r
hosts={}
for name in read(S/'results.json')['shards']:
 for line in gzip.open(S/name,'rt'):
  r=json.loads(line)
  if r['global_index'] in wanted:
   assert r['receipt']['status']=='COMPLETE';hosts[r['global_index']]=r['receipt']['solutions']
edges_checked=0;tree_nodes=0;tree_branches=0
for (gid,j),cert in certs.items():
 assert time.monotonic()-start<60
 g=[set(ns) for ns in inputs[gid]['neighbors']]
 for e,m in enumerate(hosts[gid][j],42):
  for v in range(49):
   if m>>v&1:g[e].add(v);g[v].add(e)
 H=set(range(7));E=set(range(42,49))
 assert all(g[u]<=H|E and len(g[u]&H)==2 for u in range(21,42))
 assert all(len(g[v]&H)==1 for v in range(7,21))
 assert all(len(g[h])==8 and not g[h]&H for h in H) and all(len(g[e])==7 for e in E)
 demand={u:7-2*len(g[u]) for u in range(21,42)};capacity={v:7-len(g[v]) for v in range(7,21)}
 assert set(demand.values())<={1,3} and set(capacity.values())<={2,3} and sum(demand.values())==sum(capacity.values())==39
 families={}
 def match(left,supports):
  if not left:return True
  v=min(left)
  return any(frozenset([v,w]) in supports and match(left-{v,w},supports) for w in left-{v})
 for u in demand:
  candidates={v for v in capacity if all(g[v].isdisjoint(g[w]) for w in g[u])};choices=[]
  for chosen in itertools.combinations(sorted(candidates),demand[u]):
   if any(g[v]&g[w] for v,w in itertools.combinations(chosen,2)):continue
   used=set().union(*(g[v]&H for v in chosen));assert len(used)==demand[u];left=H-used
   pairs={v for v in demand if v!=u and g[v]&H<=left and all(g[v].isdisjoint(g[w]) for w in g[u]|set(chosen))}
   supports={frozenset(g[v]&H) for v in pairs};assert all(len(e)==2 for e in supports)
   if match(left,supports):choices.append(frozenset(chosen))
  families[u]=choices
 assert all(families.values())
 saved={int(k):[frozenset(i+7 for i in range(14) if mask>>i&1) for mask in masks] for k,masks in cert['families'].items()}
 assert set(saved)==set(families) and all(set(saved[u])==set(families[u]) and len(saved[u])==len(families[u]) for u in families)
 assert cert['status']=='INFEASIBLE_PROJECTION' and cert['witness'] is None
 assert cert['capacity']==[capacity[v] for v in range(7,21)]
 fs={u:[frozenset(i+7 for i in range(14) if mask>>i&1) for mask in cert['families'][str(u)]] for u in families}
 order=cert['order'];assert len(order)==21 and set(order)==set(fs)
 tree=cert['tree'];seen=set()
 def visit(index,depth,chosen,usage):
  global tree_nodes,tree_branches
  assert time.monotonic()-start<60 and 0<=index<len(tree) and index not in seen and depth<21
  seen.add(index);tree_nodes+=1;node=tree[index];assert node['depth']==depth and 'witness' not in node
  u=order[depth];branches=node['branches'];assert [b['family'] for b in branches]==list(range(len(fs[u])))
  for branch in branches:
   tree_branches+=1;f=fs[u][branch['family']]
   if 'capacity_reject' in branch:
    v=branch['capacity_reject']+7;assert v in f and usage.get(v,0)>=capacity[v]
   elif 'common_neighbour_reject' in branch:
    v=branch['common_neighbour_reject'];assert v in chosen and len(f&chosen[v])+len(g[u]&g[v])>1
   else:
    assert set(branch)=={'family','child'}
    assert all(usage.get(v,0)<capacity[v] for v in f) and all(len(f&h)+len(g[u]&g[v])<=1 for v,h in chosen.items())
    next_usage=usage.copy()
    for v in f:next_usage[v]=next_usage.get(v,0)+1
    visit(branch['child'],depth+1,dict(chosen)|{u:f},next_usage)
 visit(0,0,{},{});assert len(seen)==len(tree)==cert['nodes']<=10000
 edges_checked+=sum(map(len,families.values()))
assert out['seconds']<l['seconds']==60
result={'status':'PASS_FULL_INCIDENCE_TREES','negative':23,'remaining':0,'families':edges_checked,'tree_nodes':tree_nodes,'tree_branches':tree_branches,'seconds':time.monotonic()-start,'manifest_sha256':sha(P/'pins.json'),'scope':'Exact refined singleton families and every negative incidence tree branch; full source composition reviewed separately.'}
(O/'REVIEW.json').write_text(json.dumps(result,indent=2)+'\n');print(result)
