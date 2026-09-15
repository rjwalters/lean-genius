"""Recheck disjoint composition and exact F12 root isomorphism."""
import gzip,hashlib,itertools,json
from pathlib import Path
P=Path(__file__).parent
R=Path('/Users/rwalters/GitHub/lean-genius/.codex/worktrees/erdos85-sol2-integration/research/problems/erdos-85-wip-01');S=R/'q7_h7_a6_f12_host/original'
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
c=read(P/'composition.json');assert sha(S/'survivors.json')==c['source_survivors_sha256'];order=list(map(tuple,read(S/'survivors.json')));assert len(order)==len(set(order))==397234
seen=set()
for part in c['parts']:
 f=Path(part['results_path']);assert sha(f)==part['results_sha256'];r=read(f)
 if 'pins_sha256' in part:assert sha(f.parent/'pins.json')==part['pins_sha256']
 if part['source']=='accepted2135':
  keys=[];visited=[];unknown=[]
  for name in r['shards']:
   for rec in map(json.loads,gzip.open(f.parent/name,'rt')):
    k=(rec['global_index'],rec['leaf_index']);assert k==order[len(visited)];visited.append(k)
    if rec['receipt']['status'] in ['INFEASIBLE_ROW','INFEASIBLE_ARC']:keys.append(k)
    else:assert rec['receipt']['status']=='UNKNOWN';unknown.append(k)
  assert len(visited)==395764 and unknown==[(227088,0)]
 elif part['source']=='incidence-projection':
  assert all(rec['status']=='INFEASIBLE_PROJECTION' for rec in r['records']) and not r['unvisited'];keys=[(rec['global_index'],rec['leaf_index']) for rec in r['records']]
 else:keys=[(rec['global_index'],rec['leaf_index']) for rec in r['certificates']]
 assert len(keys)==len(set(keys))==part['negative_count'] and not seen.intersection(keys);seen.update(keys)
assert seen==set(order) and c['covered']==397234 and c['remaining']==0
m=read(P/'root-mapping.json');assert m['root']['id']=='cube_F6_t17' and m['root']['mask']==331907 and m['source_F_index']==12
perm=m['parent_to_source'];assert sorted(perm)==list(range(7));edges=[e for i,e in enumerate(itertools.combinations(range(7),2)) if 331907>>i&1]
assert {tuple(sorted((perm[u],perm[v]))) for u,v in edges}==set(map(tuple,m['source_edges']))
A=R/'q7_h7_a6_high_pairing_cover/original/source-cover-results.json';assert sha(A)==m['source_cover_sha256'] and read(A)['cases'][12]['F_edges']==m['source_edges']
assert [r['id'] for r in read(P/'premises.json')]==[2118,2122,2125,2130,2135,2705,2706,2708,2711,2712]
assert all(r['status']=='resolved' and r['resolution'].startswith('PASS') for r in read(P/'premises.json'))
print('PASS exact397234leaf disjoint cover and rootF12 mapping; endpoint validity is supplied by named reviews and projection verifier.')
