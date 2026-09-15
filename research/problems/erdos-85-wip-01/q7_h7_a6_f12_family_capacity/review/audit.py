import gzip,hashlib,itertools,json,sqlite3,time
from pathlib import Path
P=Path('/Users/rwalters/lean-genius-h7-a6-f12-triangle-family-sol2-20260915');T=Path('/Users/rwalters/lean-genius-h7-a6-f12-hall-capacity-sol2-20260915');O=Path(__file__).parent
S=Path('/Users/rwalters/GitHub/lean-genius/.codex/worktrees/erdos85-sol2-integration/research/problems/erdos-85-wip-01/q7_h7_a6_f12_host/original')
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for d in [P,T,S]:
 for n,h in read(d/'pins.json').items():assert sha(d/n)==h
l=read(P/'launch.json');assert l['source_manifest']==sha(T/'pins.json') and l['host_manifest']==sha(S/'pins.json') and l['driver']==sha(P/'probe.py')
c=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True)
st,res=c.execute('select status,resolution from review_requests where id=2708').fetchone();assert st=='resolved' and res==l['review2708'] and res.startswith('PASS')
start=time.monotonic();out=read(P/'results.json');expected=set(map(tuple,read(T/'results.json')['remaining']));certs={(x['global_index'],x['leaf_index']):x for x in out['certificates']};rem=set(map(tuple,out['remaining']))
assert len(expected)==29 and len(certs)==len(out['certificates'])==out['killed']==5 and len(rem)==len(out['remaining'])==24 and not certs.keys()&rem and certs.keys()|rem==expected
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
edges_checked=0
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
 eligible={};families={}
 for u in demand:
  candidates={v for v in capacity if all(g[v].isdisjoint(g[w]) for w in g[u])}
  if demand[u]==3:
   allowed=set();choices=[]
   for tri in itertools.combinations(sorted(candidates),3):
    if any(g[v]&g[w] for v,w in itertools.combinations(tri,2)):continue
    used=set().union(*(g[v]&H for v in tri));assert len(used)==3
    left=H-used
    pairs={v for v in demand if v!=u and g[v]&H<=left and all(g[v].isdisjoint(g[w]) for w in g[u]|set(tri))}
    supports={frozenset(g[v]&H) for v in pairs}
    if any(frozenset(left-e) in supports for e in supports):allowed.update(tri);choices.append(frozenset(tri))
   candidates=allowed
   families[u]=choices
  eligible[u]=candidates
  if demand[u]==1:families[u]=[frozenset([v]) for v in candidates]
 assert all(families.values())
 saved={int(k):[frozenset(i+7 for i in range(14) if mask>>i&1) for mask in masks] for k,masks in cert['families'].items()}
 assert set(saved)==set(families) and all(set(saved[u])==set(families[u]) and len(saved[u])==len(families[u]) for u in families)
 mask=cert['singleton_mask'];assert 0<mask<(1<<14)-1;K={i+7 for i in range(14) if mask>>i&1}
 actual=sum(capacity[v] for v in K);lower=sum(min(len(f&K) for f in choices) for choices in families.values());upper=sum(max(len(f&K) for f in choices) for choices in families.values())
 assert (actual,lower,upper)==(cert['capacity'],cert['lower'],cert['upper']) and not lower<=actual<=upper
 edges_checked+=sum(map(len,families.values()))
assert out['seconds']<l['seconds']==60
result={'status':'PASS_FAMILY_CAPACITY_CERTIFICATES','negative':5,'remaining':24,'families':edges_checked,'seconds':time.monotonic()-start,'manifest_sha256':sha(P/'pins.json'),'scope':'Whole singleton-family subset capacity certificates only; no fullF12/Lean/global exclusion.'}
(O/'REVIEW.json').write_text(json.dumps(result,indent=2)+'\n');print(result)
