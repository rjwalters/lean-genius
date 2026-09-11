from pathlib import Path
import json,hashlib
s=Path('/tmp/erdos85-sol1-q9-order3-f2-integral-attempt');p=Path(__file__).parent
pins=json.loads((s/'pins.json').read_text())
for f,h in pins.items():assert hashlib.sha256((s/f).read_bytes()).hexdigest()==h
for f,h in json.loads((s/'input-pins.json').read_text()).items():assert hashlib.sha256(Path(f).read_bytes()).hexdigest()==h
r=json.loads((s/'receipts.json').read_text());rows=r['roots'];assert [x['root'] for x in rows]==list(range(117))
assert r['original_aggregate_seconds']==180 and r['original_per_root_seconds']==2 and r['original_node_limit']==1000
assert {int(f.stem.split('-')[1]) for f in s.glob('numerical-*.json')}==set(range(87))
for x in rows[:87]:
 n=json.loads((s/f"numerical-{x['root']}.json").read_text())
 assert x['status']=='UNKNOWN' and x['solver_status']==n['solver_status']==1 and n['root']==x['root'] and n['x'] is None
 assert 'Time limit' in n['message'] and n['mip_node_count'] is None
 assert 0<x['allocated_seconds']<=2 and x['seconds']>=0
assert all(x=={'root':i,'status':'UNVISITED'} for i,x in enumerate(rows[87:],87))
assert not list(s.glob('witness-*.json'))
assert all(x['allocated_seconds']==2 for x in rows[:86]) and rows[86]['allocated_seconds']<2
assert sum(x['seconds'] for x in rows[:87])<=r['elapsed_seconds']
(p/'source-pins.json').write_bytes((s/'pins.json').read_bytes());(p/'results.json').write_text(json.dumps({'status':'PASS_RECEIPTS_ONLY','source_files':len(pins),'UNKNOWN':87,'UNVISITED':30,'witnesses':0,'elapsed_seconds':r['elapsed_seconds'],'last_allocation':rows[86]['allocated_seconds'],'solve_replay':False},indent=2)+'\n');print(len(pins),'sourcepins verified;87UNKNOWN/30UNVISITED;no witness or replay')
