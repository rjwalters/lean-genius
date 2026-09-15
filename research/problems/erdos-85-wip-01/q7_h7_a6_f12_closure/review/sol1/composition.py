import hashlib,itertools,json,sqlite3
from pathlib import Path
P=Path('/Users/rwalters/lean-genius-h7-a6-f12-incidence-projection-sol2-20260915');O=Path(__file__).parent
R=Path('/Users/rwalters/GitHub/lean-genius/.codex/worktrees/erdos85-sol2-integration/research/problems/erdos-85-wip-01');S=R/'q7_h7_a6_f12_host/original';F=R/'q7_h7_a6_f12_residual_frontier/original'
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for d,m in [(P,'pins.json'),(S,'pins.json'),(F,'final-pins.json')]:
 for n,h in read(d/m).items():assert sha(d/n)==h
comp=read(P/'composition.json');keys=list(map(tuple,read(S/'survivors.json')));assert len(keys)==len(set(keys))==397234 and sha(S/'survivors.json')==comp['source_survivors_sha256']
old=read(F/'results.json');assert old['visited']==395764 and old['retained']==[[227088,0,'UNKNOWN']] and read(F/'input-survivors.json')==read(S/'survivors.json')
covered=set(keys[:old['visited']])-{(227088,0)};assert len(covered)==395763
counts=[len(covered)]
for part in comp['parts']:
 p=Path(part['results_path']);assert sha(p)==part['results_sha256'];result=read(p)
 if part['source']=='accepted2135':assert p==F/'results.json' and part['negative_count']==395763;continue
 if 'pins_sha256' in part:
  assert sha(p.parent/'pins.json')==part['pins_sha256']
  for n,h in read(p.parent/'pins.json').items():assert sha(p.parent/n)==h
 records=result['records'] if part['source']=='incidence-projection' else result['certificates']
 if part['source']=='incidence-projection':assert all(r['status']=='INFEASIBLE_PROJECTION' for r in records)
 new={(r['global_index'],r['leaf_index']) for r in records};assert len(new)==len(records)==part['negative_count'] and not covered&new and new<=set(keys)
 covered|=new;counts.append(len(new))
assert counts==[395763,1253,89,100,5,1,23] and covered==set(keys) and comp['remaining']==0
m=read(P/'root-mapping.json');src=R/'q7_h7_a6_high_pairing_cover/original/source-cover-results.json';scope=R/'h7-frontier-map-20260915/overlay-a6f16-f17-20260915/author/results.json'
assert sha(src)==m['source_cover_sha256'] and sha(scope)==m['scope_map_sha256']
root=next(r for r in read(scope)['rows'] if r['id']=='cube_F6_t17');assert root==m['root'] and root['mask']==331907 and m['source_F_index']==12
f=next(r for r in read(src)['cases'] if r['F_index']==12);assert f['F_edges']==m['source_edges'];perm=m['parent_to_source'];assert perm==[0,4,5,2,1,3,6]
assert {tuple(sorted((perm[u],perm[v]))) for i,(u,v) in enumerate(itertools.combinations(range(7),2)) if root['mask']>>i&1}==set(map(tuple,f['F_edges']))
host=read(S/'results.json');assert host['counts']=={'COMPLETE':16040} and host['unvisited']==0 and host['leaves']==397234
c=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True)
for rid in [2118,2122,2125,2130,2135,2705,2706,2708,2711,2712]:
 st,res=c.execute('select status,resolution from review_requests where id=?',(rid,)).fetchone();assert st=='resolved' and res.startswith('PASS')
a=read(O/'REVIEW.json');assert a['negative']==23 and a['remaining']==0 and a['tree_nodes']==134 and a['tree_branches']==223
l=read(P/'launch.json');assert l['nodes_per_case']==10000 and read(P/'results.json')['seconds']<l['seconds']==60 and (P/'results.json').stat().st_size<l['artifact_bytes']==50000000
out={'status':'PASS_REVIEW2713','root':root,'parent_to_source':perm,'parts':counts,'covered':397234,'remaining':0,'tree_audit':a,'author_manifest_sha256':sha(P/'pins.json'),'scope':'Whole a6 F12 necessary structural graph-cover exclusion; all historic capped evidence unchanged. No arbitrary CNF UNSAT, Lean, wholeH7/global proof.'}
(O/'REVIEW2713.json').write_text(json.dumps(out,indent=2)+'\n');print({'status':out['status'],'counts':counts,'covered':len(covered)})
