import hashlib,json,sqlite3
from pathlib import Path
P=Path('/Users/rwalters/lean-genius-h7-f0-pairrow-sol2-20260915');O=Path(__file__).parent
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in read(P/'residual-pins.json').items():assert sha(P/n)==h
for n,h in read(O/'residual-audit/launch.json')['pins'].items():assert sha(Path(n))==h
launch=read(P/'residual/launch.json')
assert launch['driver_sha256']==sha(P/'residual.py')
assert launch['host_pins_sha256']==sha(P/'host-pins.json')
assert launch['aggregate_seconds']==30 and launch['max_nodes']==100000
for n,h in launch['api_pins'].items():assert sha(Path(launch['api_path'])/n)==h
r=read(P/'residual/results.json');a=read(O/'residual-audit/result.json')
assert r['visited']==r['total']==3012 and r['unvisited']==0 and not r['retained']
assert r['counts']=={'INFEASIBLE_ARC':3012} and r['seconds']<30
assert a['whole_negative_cover'] and a['counts']==r['counts'] and a['seconds']<90
assert read(O/'REVIEW2674.json')['status']=='PASS_REVIEW2674'
c=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True)
for rid in (2111,2116,2117,2654,2674):
    rr=c.execute('select status,resolution from review_requests where id=?',(rid,)).fetchone();assert rr[0]=='resolved' and rr[1].startswith('PASS')
out={'status':'PASS_REVIEW2675','root':'cube_F7_t0','mask':139591,'high_inputs':18408,'host_negative_inputs':17700,'residual_leaves':3012,'all_residual_leaves_negative':True,'independent_domains':a['domains'],'independent_rows':a['rows'],'independent_arc_events':a['arc_events'],'independent_removals':a['removed_rows'],'independent_seconds':a['seconds'],'producer_residual_pins_sha256':sha(P/'residual-pins.json'),'scope':'Whole F0 structural graph-cover exclusion conditional on reviewed upstream2116 enumeration-code completeness. No Lean kernel theorem, arbitrary CNF UNSAT, whole H7 or global Erdős85 claim.'}
(O/'REVIEW2675.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
