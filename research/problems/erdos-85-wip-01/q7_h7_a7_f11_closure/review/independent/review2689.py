import hashlib,json,sqlite3
from pathlib import Path
P=Path('/Users/rwalters/lean-genius-h7-f11-sol2-20260915');O=Path(__file__).parent
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in read(P/'residual-pins.json').items():assert sha(P/n)==h
for n,h in read(O/'residual-audit/launch.json')['pins'].items():assert sha(Path(n))==h
l=read(P/'residual/launch.json');r=read(P/'residual/results.json');a=read(O/'residual-audit/result.json')
assert l['driver_sha256']==sha(P/'residual.py') and l['host_pins_sha256']==sha(P/'host-pins.json')
assert l['aggregate_seconds']==120 and l['max_nodes']==100000 and r['seconds']<120
for n,h in l['api_pins'].items():assert sha(Path(l['api_path'])/n)==h
assert r['counts']=={'INFEASIBLE_ROW':548022,'INFEASIBLE_ARC':10697}==a['counts']
assert r['total']==r['visited']==a['leaves']==558719 and not r['unvisited'] and not r['retained']
assert a['whole_negative_cover'] and a['seconds']<90
c=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True)
for rid in (2111,2116,2117,2683,2684,2688):
    status,res=c.execute('select status,resolution from review_requests where id=?',(rid,)).fetchone();assert status=='resolved' and res.startswith('PASS')
root=read(P/'f11-root-mapping.json');assert root['matches'][0]['root']['id']=='cube_F7_t11' and root['matches'][0]['root']['mask']==401671
out={'status':'PASS_REVIEW2689','root':'cube_F7_t11','mask':401671,'high_inputs':149309,'host_negative_inputs':28939,'residual_leaves':558719,'counts':a['counts'],'independent_domains':a['domains'],'independent_rows':a['rows'],'independent_arc_events':a['arc_events'],'independent_removals':a['removed_rows'],'independent_seconds':a['seconds'],'producer_residual_pins_sha256':sha(P/'residual-pins.json'),'scope':'Whole F11 structural graph-cover exclusion conditional on reviewed2116 enumeration-code completeness. No Lean kernel, arbitrary CNF UNSAT, whole H7 or global Erdős85 proof.'}
(O/'REVIEW2689.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
