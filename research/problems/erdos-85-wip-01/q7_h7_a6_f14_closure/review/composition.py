"""Exact F14 source partition; certificate truth is an explicit separate audit."""
import hashlib,itertools,json,sqlite3,subprocess
from pathlib import Path
D=Path(__file__).parent;B=Path('/Users/rwalters/lean-genius-h7-a6-f14-sol1-20260915');T=Path('/Users/rwalters/lean-genius-h7-a6-f14-triangle-sol1-20260915');P=Path('/Users/rwalters/lean-genius-h7-a6-f14-incidence-cover-sol2-20260915');repo=Path('/Users/rwalters/GitHub/lean-genius/.codex/worktrees/erdos85-sol2-integration');R=repo/'research/problems/erdos-85-wip-01'
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for base,manifest in [(B,'host-pins.json'),(B,'residual-pins.json'),(T,'pins.json')]:
 for n,h in read(base/manifest).items():assert sha(base/n)==h
c=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True);reviews={}
for rid in [2118,2122,2125,2703,2707,2714,2716,2717,2715]:
 st,res=c.execute('select status,resolution from review_requests where id=?',(rid,)).fetchone();assert st=='resolved' and res.startswith('PASS');reviews[rid]=res
keys=list(map(tuple,read(B/'hosts/survivors.json')));assert len(keys)==len(set(keys))==2278608
prefix=read(B/'residual/results.json');assert prefix['visited']==1757882 and prefix['unvisited']==520726 and prefix['stop']=='ARTIFACT_CAP' and not prefix['retained']
tri=read(T/'repaired/results.json');neg=set((gid,j) for gid,j,u in tri['certificates']);remaining=set(map(tuple,tri['remaining']))
assert len(neg)==len(tri['certificates'])==75027 and len(remaining)==len(tri['remaining'])==445699
assert neg.isdisjoint(remaining) and neg|remaining==set(keys[1757882:])
current=read(P/'results.json');assert current['total']==current['visited']==445699 and current['unvisited']==current['computed_not_saved']==0 and not current['retained'] and current['stop'] is None
assert current['counts']=={'INFEASIBLE_PROJECTION':175232,'EMPTY_FAMILY':270467}
assert read(P/'unvisited.json')==[]
assert len(keys[:1757882])+len(neg)+len(remaining)==len(keys)
m=read(B/'root-mapping.json');source=R/'q7_h7_a6_high_pairing_cover/original/source-cover-results.json';assert sha(source)==m['source_cover_sha256']
assert m['source_edges']==next(x['F_edges'] for x in read(source)['cases'] if x['F_index']==14)
perm=m['parent_to_source'];assert sorted(perm)==list(range(7))
root=m['root'];assert root['id']=='cube_F6_t18' and root['mask']==594051
edges={tuple(sorted((perm[u],perm[v]))) for i,(u,v) in enumerate(itertools.combinations(range(7),2)) if root['mask']>>i&1};assert edges==set(map(tuple,m['source_edges']))
map_path='research/problems/erdos-85-wip-01/h7-frontier-map-20260915/overlay-a6f12-20260915/author/results.json'
previous=json.loads(subprocess.check_output(['git','show','97ec983fce:'+map_path],cwd=repo));assert previous['counts']=={'total':28,'covered':27,'residual':1} and previous['residual']==[root['id']]
assert next(x for x in previous['rows'] if x['id']==root['id'])==root
out={'status':'PASS_EXACT_F14_PARTITION_AND_ROOT','counts':[1757882,75027,445699],'total':2278608,'root':root,'source_F_index':14,'parent_to_source':perm,'source_cover_sha256':sha(source),'previous_map_revision':'97ec983fce','reviews':reviews,'scope':'Disjoint exact source partition and root mapping. Last 445699 certificate truths require separate independent audit; no closure promotion from this file alone.'}
(D/'COMPOSITION_REVIEW.json').write_text(json.dumps(out,indent=2)+'\n');print({k:v for k,v in out.items() if k not in ['reviews','root']})
