"""Check pinned package and independently expanded unresolved frontier."""
import hashlib
import json
from pathlib import Path

SRC=Path('/Users/rwalters/lean-genius-h7-f2-sol2-20260915')
OUT=Path(__file__).parent
def read(p): return json.loads(p.read_text())
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()

pins=read(SRC/'residual-pins.json')
for name,h in pins.items(): assert sha(SRC/name)==h,name
launch=read(SRC/'residual/launch.json')
assert launch['driver_sha256']==sha(SRC/'residual.py')
for name,h in launch['api_pins'].items():
    assert sha(Path(launch['api_path'])/name)==h,name
front=read(SRC/'residual/frontier.json')
actual=read(OUT/'unvisited.json')
expanded=[]
high=read(SRC/'high-results.json')['results']
for g in front['unvisited_groups']:
    ci,pi=g['case_index'],g['pairing_index']
    assert (g['source_index'],g['singleton_index'])==(high[ci]['source_index'],high[ci]['singleton_index'])
    expanded.extend([ci,pi,li] for li in range(g['first_unvisited_leaf'],g['first_unvisited_leaf']+g['unvisited_count']))
assert expanded==actual and len(expanded)==79532==front['unvisited_leaves']
result=read(SRC/'residual/results.json')
unknown=[[x['case_index'],x['pairing_index'],x['leaf_index'],'UNKNOWN'] for x in front['unknown']]
assert unknown==result['retained']==[[3710,1,9,'UNKNOWN']]
for x in front['unknown']:
    assert (x['source_index'],x['singleton_index'])==(high[x['case_index']]['source_index'],high[x['case_index']]['singleton_index'])
unresolved=actual+[r[:3] for r in unknown]
remaining=sorted({high[ci]['source_index'] for ci,pi,li in unresolved})
assert remaining==front['remaining_source_indices']==[82,93]
source=Path('/Users/rwalters/GitHub/lean-genius/.codex/worktrees/erdos85-sol2-integration/research/problems/erdos-85-wip-01/q7_h7_a7_noncycle_singleton_projection/author')
for name,h in read(SRC/'high-launch.json')['source_pins'].items(): assert sha(source/name)==h
reps=read(source/'results.json')['representatives']
f2={i for i,r in enumerate(reps) if r['F_index']==2}
assert len(f2)==48 and set(remaining)<=f2 and len(f2-set(remaining))==46
assert sum((SRC/'residual'/n).stat().st_size for n in result['receipt_shards'])==result['artifact_bytes']<=150000000
assert all((SRC/'residual'/n).stat().st_size<50000000 for n in result['receipt_shards'])
out={'status':'PASS_PINS_AND_FRONTIER','package_pins':len(pins),'remaining_source_indices':remaining,
     'source_bases_without_remaining_leaves':46,'unknown':unknown,'unvisited':len(actual),
     'unresolved':len(unresolved),'scope':'Conditional on accepted upstream covers and negative endpoint soundness; no F2 exclusion.'}
(OUT/'frontier-result.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
