"""Exact certificate audit with independently rebuilt set families; no LP."""
import gzip,hashlib,itertools,json,time
from pathlib import Path
D=Path(__file__).parent;T=Path('/Users/rwalters/lean-genius-h7-a6-f12-triangle-family-sol2-20260915')
R=Path('/Users/rwalters/GitHub/lean-genius/.codex/worktrees/erdos85-sol2-integration/research/problems/erdos-85-wip-01');S=R/'q7_h7_a6_f12_host/original'
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for base in [T,S]:
 for n,h in read(base/'pins.json').items():assert sha(base/n)==h,n
l=read(D/'launch.json');assert sha(D/'probe.py')==l['driver'] and sha(T/'pins.json')==l['source_manifest'] and sha(S/'pins.json')==l['host_manifest']
r=read(D/'results.json');expected=set(map(tuple,read(T/'results.json')['remaining']));keys=[(c['global_index'],c['leaf_index']) for c in r['certificates']];rest=list(map(tuple,r['remaining']))
assert len(keys)==len(set(keys))==1 and len(rest)==len(set(rest))==23 and not r['unvisited'] and set(keys).isdisjoint(rest) and set(keys)|set(rest)==expected
ids={gid for gid,j in keys};inputs={a['global_index']:a for a in map(json.loads,gzip.open(S/'inputs.jsonl.gz','rt')) if a['global_index'] in ids};hosts={}
for name in read(S/'results.json')['shards']:
 for a in map(json.loads,gzip.open(S/name,'rt')):
  if a['global_index'] in ids:hosts[a['global_index']]=a['receipt']
start=time.monotonic();members=0
for c in r['certificates']:
 gid,j=c['global_index'],c['leaf_index'];g=[set(ns) for ns in inputs[gid]['neighbors']]
 for e,m in zip(hosts[gid]['empty_vertices'],hosts[gid]['solutions'][j]):
  for v in range(49):
   if m>>v&1:g[e].add(v);g[v].add(e)
 high=set(range(7));fs={};capacity=[7-len(g[s]) for s in range(7,21)]
 for p in range(21,42):
  assert time.monotonic()-start<60
  demand=7-2*len(g[p]);assert demand in [1,3]
  candidates=[s for s in range(7,21) if all(g[s].isdisjoint(g[w]) for w in g[p])];rows=[]
  for chosen in itertools.combinations(candidates,demand):
   if any(not g[a].isdisjoint(g[b]) for a,b in itertools.combinations(chosen,2)):continue
   covered=set().union(*(g[s]&high for s in chosen));assert len(covered)==demand;left=high-covered
   supports={frozenset(g[q]&high) for q in range(21,42) if q!=p and (g[q]&high)<=left and all(g[q].isdisjoint(g[w]) for w in g[p]|set(chosen))}
   if any(all(frozenset(order[i:i+2]) in supports for i in range(0,len(order),2)) for order in itertools.permutations(sorted(left))):rows.append(sum(1<<(s-7) for s in chosen))
  fs[p]=rows;members+=len(rows)
 assert {str(p):sorted(rows) for p,rows in fs.items()}=={p:sorted(rows) for p,rows in c['families'].items()}
 if c['kind']=='EMPTY_FAMILY':assert not fs[c['pair_vertex']]
 else:
  assert c['kind']=='WEIGHT_CAPACITY' and all(fs.values());weights=c['weights'];assert len(weights)==14 and all(type(w)==int for w in weights)
  minimum=sum(min(sum(w for s,w in enumerate(weights) if f>>s&1) for f in rows) for rows in fs.values());actual=sum(w*a for w,a in zip(weights,capacity))
  assert minimum==c['minimum']==-51 and actual==c['capacity']==-55 and minimum>actual
out={'status':'PASS_EXACT_WEIGHT_CAPACITY','negative_certificates':len(keys),'family_members':members,'remaining':23,'combined_negative_leaves':397211,'total_host_leaves':397234,'seconds':time.monotonic()-start,'scope':'Exact reconstructed necessary families and integer inequality only; no LP status relied on. Remaining23 unclassified.'}
(D/'verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
