import hashlib,itertools,json,sqlite3
from pathlib import Path
P=Path('/Users/rwalters/lean-genius-h7-a6-f16-sol2-20260915');O=Path(__file__).parent
R=Path('/Users/rwalters/GitHub/lean-genius/.codex/worktrees/erdos85-sol2-integration/research/problems/erdos-85-wip-01')
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in read(P/'residual-pins.json').items():assert sha(P/n)==h
for n,h in read(O/'residual-audit/launch.json')['input_pins'].items():assert sha(Path(n))==h
r=read(P/'residual/results.json');a=read(O/'residual-audit/REVIEW.json');l=read(P/'residual/launch.json')
assert r['counts']==a['counts']=={'INFEASIBLE_ROW':379324,'INFEASIBLE_ARC':120956}
assert r['total']==r['visited']==a['leaves']==500280 and not r['retained'] and not r['unvisited'] and a['whole_negative_cover']
assert r['seconds']<l['aggregate_seconds']==120 and a['seconds']<120 and l['max_nodes']==100000
assert sum((P/'residual'/n).stat().st_size for n in r['shards'])==r['artifact_bytes']<l['artifact_byte_cap']==150000000
assert l['source_pins_sha256']==sha(P/'host-pins.json') and l['driver_sha256']==sha(P/'residual.py')
for n,h in read(Path(l['api_path'])/'pins.json').items():assert sha(Path(l['api_path'])/n)==h
root=next(x for x in read(R/'h7-frontier-map-20260915/overlay-f10-f13-a6f13-20260915/author/results.json')['rows'] if x['id']=='cube_F6_t15');assert root['mask']==622659
F=next(x for x in read(R/'q7_h7_a6_high_pairing_cover/original/source-cover-results.json')['cases'] if x['F_index']==16);perm=[2,3,4,0,1,6,5]
assert {tuple(sorted((perm[u],perm[v]))) for i,(u,v) in enumerate(itertools.combinations(range(7),2)) if root['mask']>>i&1}==set(map(tuple,F['F_edges']))
c=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True)
for rid in [2118,2122,2125,2699,2701,2120,2126]:
 st,res=c.execute('select status,resolution from review_requests where id=?',(rid,)).fetchone();assert st=='resolved' and res.startswith('PASS')
out={'status':'PASS_REVIEW2704','root':root,'source_F_index':16,'parent_to_source':perm,'residual_count':500280,'audit':a,'author_manifest_sha256':sha(P/'residual-pins.json'),'scope':'Whole a6F16 necessary structural graph-cover exclusion, not arbitrary CNF/Lean/global proof.'}
(O/'REVIEW2704.json').write_text(json.dumps(out,indent=2)+'\n')
names=['audit_residual.py','residual-audit/launch.json','residual-audit/REVIEW.json','final_residual_review.py','REVIEW2704.json']
(O/'residual-review-pins.json').write_text(json.dumps({n:sha(O/n) for n in names},indent=2)+'\n');print('PASS',out['status'])
