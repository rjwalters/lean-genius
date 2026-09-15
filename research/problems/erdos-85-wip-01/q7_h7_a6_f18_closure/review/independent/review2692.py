import hashlib,itertools,json,sqlite3
from pathlib import Path
P=Path('/Users/rwalters/lean-genius-h7-a6-f18-sol2-20260915');O=Path(__file__).parent
R=Path('/Users/rwalters/GitHub/lean-genius/.codex/worktrees/erdos85-sol2-integration/research/problems/erdos-85-wip-01')
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in read(P/'pins.json').items():assert sha(P/n)==h
for n,h in read(O/'launch.json')['input_pins'].items():assert sha(Path(n))==h
m=read(P/'root-mapping.json');sm=R/'h7-frontier-map-20260915/overlay-f8-20260915/author/results.json';src=R/'q7_h7_a6_high_pairing_cover/original/source-cover-results.json'
assert sha(sm)==m['scope_map_sha256'] and sha(src)==m['source_cover_sha256']
root=next(r for r in read(sm)['rows'] if r['id']=='cube_F6_t16');assert root==m['root'] and root['mask']==1085571
perm=m['parent_to_source'];assert sorted(perm)==list(range(7)) and perm==[0,5,6,2,1,3,4]
edges=[e for i,e in enumerate(itertools.combinations(range(7),2)) if root['mask']>>i&1]
assert {tuple(sorted((perm[u],perm[v]))) for u,v in edges}==set(map(tuple,m['source_edges']))
case=next(r for r in read(src)['cases'] if r['F_index']==18);assert case['F_edges']==m['source_edges']
c=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True)
for rid in (2118,2122,2125,2120,2126,2133):
    st,res=c.execute('select status,resolution from review_requests where id=?',(rid,)).fetchone();assert st=='resolved' and res.startswith('PASS')
a=read(O/'REVIEW.json');r=read(P/'results.json');assert a['whole_negative_cover'] and a['counts']==r['counts']=={'INFEASIBLE_ROW':252219,'INFEASIBLE_ARC':79777}
assert r['visited']==r['total']==331996 and not r['unvisited'] and not r['retained'] and r['seconds']<90
assert a['seconds']<120 and sum((P/n).stat().st_size for n in r['shards'])==r['artifact_bytes']<150000000
out={'status':'PASS_REVIEW2692','root':'cube_F6_t16','source_F_index':18,'mask':1085571,'parent_to_source':perm,'leaves':331996,'domains':a['domains'],'rows':a['rows'],'arc_events':a['arc_events'],'removed_rows':a['removed_rows'],'independent_seconds':a['seconds'],'source_manifest_sha256':sha(P/'pins.json'),'scope':'Whole a6 F18 structural graph-cover exclusion using reviewed complete2118/2122/2125/2133 source and host covers. No arbitrary CNF UNSAT, Lean kernel, whole H7 or global theorem.'}
(O/'REVIEW2692.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
