import gzip,hashlib,itertools,json,sqlite3,time
from pathlib import Path
P=Path('/Users/rwalters/lean-genius-h7-a6-f12-weighted-family-sol2-20260915');T=Path('/Users/rwalters/lean-genius-h7-a6-f12-triangle-family-sol2-20260915');O=Path(__file__).parent
S=Path('/Users/rwalters/GitHub/lean-genius/.codex/worktrees/erdos85-sol2-integration/research/problems/erdos-85-wip-01/q7_h7_a6_f12_host/original')
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for d in [P,T,S]:
 for n,h in read(d/'pins.json').items():assert sha(d/n)==h
l=read(P/'launch.json');assert l['source_manifest']==sha(T/'pins.json') and l['host_manifest']==sha(S/'pins.json') and l['driver']==sha(P/'probe.py')
c=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True)
st,res=c.execute('select status,resolution from review_requests where id=2711').fetchone();assert st=='resolved' and res==l['review2711'] and res.startswith('PASS')
start=time.monotonic();out=read(P/'results.json');expected=set(map(tuple,read(T/'results.json')['remaining']));certs={(x['global_index'],x['leaf_index']):x for x in out['certificates']};rem=set(map(tuple,out['remaining']))
assert len(expected)==24 and len(certs)==len(out['certificates'])==out['killed']==1 and len(rem)==len(out['remaining'])==23 and not certs.keys()&rem and certs.keys()|rem==expected
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
 weights=cert['weights'];assert len(weights)==14 and all(type(w)==int for w in weights) and cert['kind']=='WEIGHT_CAPACITY'
 minimum=sum(min(sum(weights[v-7] for v in f) for f in choices) for choices in families.values());actual=sum(capacity[v]*weights[v-7] for v in capacity)
 assert minimum==cert['minimum']==-51 and actual==cert['capacity']==-55 and minimum>actual
 edges_checked+=sum(map(len,families.values()))
assert out['seconds']<l['seconds']==60
result={'status':'PASS_WEIGHTED_FAMILY_CERTIFICATE','negative':1,'remaining':23,'families':edges_checked,'seconds':time.monotonic()-start,'manifest_sha256':sha(P/'pins.json'),'scope':'Exact refined family matching and signed integer capacity certificate, no LP trust or wholeF12/Lean/global exclusion.'}
(O/'REVIEW.json').write_text(json.dumps(result,indent=2)+'\n');print(result)
