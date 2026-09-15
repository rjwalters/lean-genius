"""Independent singleton-family subset inequalities; set adjacency reconstruction."""
import gzip,hashlib,itertools,json,time
from pathlib import Path
D=Path(__file__).parent;T=Path('/Users/rwalters/lean-genius-h7-a6-f12-hall-capacity-sol2-20260915')
R=Path('/Users/rwalters/GitHub/lean-genius/.codex/worktrees/erdos85-sol2-integration/research/problems/erdos-85-wip-01');S=R/'q7_h7_a6_f12_host/original'
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for base in [T,S]:
 for n,h in read(base/'pins.json').items():assert sha(base/n)==h,n
launch=read(D/'launch.json');assert sha(D/'probe.py')==launch['driver'] and sha(T/'pins.json')==launch['source_manifest'] and sha(S/'pins.json')==launch['host_manifest']
r=read(D/'results.json');expected=set(map(tuple,read(T/'results.json')['remaining']));keys=[(c['global_index'],c['leaf_index']) for c in r['certificates']];remaining=list(map(tuple,r['remaining']))
assert len(keys)==len(set(keys))==5 and len(remaining)==len(set(remaining))==24 and set(keys).isdisjoint(remaining) and set(keys)|set(remaining)==expected
ids={gid for gid,j in expected};inputs={a['global_index']:a for a in map(json.loads,gzip.open(S/'inputs.jsonl.gz','rt')) if a['global_index'] in ids};hosts={}
for name in read(S/'results.json')['shards']:
 for a in map(json.loads,gzip.open(S/name,'rt')):
  if a['global_index'] in ids:hosts[a['global_index']]=a['receipt']
start=time.monotonic();triangle_tests=0;deficiencies=[]
for c in r['certificates']:
 assert time.monotonic()-start<60
 gid,j=c['global_index'],c['leaf_index'];g=[set(ns) for ns in inputs[gid]['neighbors']]
 for e,m in zip(hosts[gid]['empty_vertices'],hosts[gid]['solutions'][j]):
  for v in range(49):
   if m>>v&1:g[e].add(v);g[v].add(e)
 high=set(range(7));pairs=list(range(21,42));singles=list(range(7,21));demand={p:7-2*len(g[p]) for p in pairs};capacity={s:7-len(g[s]) for s in singles}
 assert sum(demand.values())==sum(capacity.values())==39 and set(demand.values())<={1,3} and set(capacity.values())<={2,3}
 families={}
 for p in pairs:
  cand=[s for s in singles if all(g[s].isdisjoint(g[w]) for w in g[p])]
  if demand[p]==3:
   allowed=[]
   for tri in itertools.combinations(cand,3):
    if any(not g[a].isdisjoint(g[b]) for a,b in itertools.combinations(tri,2)):continue
    covered=set().union(*(g[s]&high for s in tri));assert len(covered)==3;left=high-covered
    qs=[q for q in pairs if q!=p and (g[q]&high)<=left and all(g[q].isdisjoint(g[w]) for w in g[p]|set(tri))]
    if any((g[a]&high).isdisjoint(g[b]&high) for a,b in itertools.combinations(qs,2)):allowed.append(sum(1<<(s-7) for s in tri))
    triangle_tests+=1
   families[p]=sorted(allowed)
  else:families[p]=[1<<(s-7) for s in cand]
 assert {str(p):sorted(ns) for p,ns in families.items()}=={p:sorted(ns) for p,ns in c['families'].items()}
 K=c['singleton_mask'];assert 0<K<(1<<14)-1
 actual=sum(capacity[s] for s in singles if K>>(s-7)&1)
 lower=sum(min((f&K).bit_count() for f in fs) for fs in families.values())
 upper=sum(max((f&K).bit_count() for f in fs) for fs in families.values())
 assert (actual,lower,upper)==(c['capacity'],c['lower'],c['upper']) and not lower<=actual<=upper
 deficiencies.append(max(lower-actual,actual-upper))
out={'status':'PASS_FAMILY_SUBSET_CERTIFICATES','negative_certificates':5,'remaining':24,'triangle_tests':triangle_tests,'min_deficiency':min(deficiencies),'max_deficiency':max(deficiencies),'combined_negative_leaves':397210,'total_host_leaves':397234,'seconds':time.monotonic()-start,'scope':'Independent set families and strict subset inequalities. Remaining24 unclassified.'}
(D/'verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
