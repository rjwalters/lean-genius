"""One declared operation-budget calibration on exactly eight saved F0 fixtures."""
import hashlib
import importlib.util
import json
import math
import sqlite3
import time
from pathlib import Path

P=Path(__file__).parent
OUT=P/'calibration-450k'
OUT.mkdir(exist_ok=True)
db=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True)
review=db.execute('select status,resolution from review_requests where id=2669').fetchone()
assert review and review[0]=='resolved' and review[1].startswith('PASS'),review
pins=json.loads((P/'pins.json').read_text())
for name,h in pins.items():assert hashlib.sha256((P/name).read_bytes()).hexdigest()==h
fixed=json.loads((P/'cached/fixed-results.json').read_text())
summary=json.loads((P/'cached/fixture-summary.json').read_text())
reserve=math.ceil(max(r['receipt']['nodes'] for r in fixed)/10000)*10000
ratios=[r['nodes']/r['prior_nodes'] for r in summary if r['status']=='COMPLETE']
factor=math.ceil(max(ratios));cap=reserve+factor*100000
assert reserve==50000 and factor==4 and cap==450000
inputs=[r for r in json.loads((P/'cached/fixture-launch.json').read_text())['inputs'] if r['F_index']==0]
assert len(inputs)==8 and all(r['prior_status']=='UNKNOWN' and r['prior_nodes']==100001 for r in inputs)
def module(name,path):
    spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
api=module('cached_host_api',P/'cached/api.py')
checker=module('independent_host_receipts',P/'cached/check_receipt.py')
with (OUT/'launch.json').open('x') as f:
    json.dump({'max_nodes':cap,'aggregate_seconds':60,'reserve':reserve,'factor':factor,'measured_ratios':ratios,
               'inputs':inputs,'source_pins_sha256':hashlib.sha256((P/'pins.json').read_bytes()).hexdigest(),
               'driver_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'review2669':review},f,indent=2)
start=time.monotonic();deadline=start+60;results=[]
for index,fixture in enumerate(inputs):
    remaining=deadline-time.monotonic()
    if remaining<=0:break
    receipt=api.enumerate_hosts(fixture['adjacency'],max_nodes=cap,seconds=remaining)
    with (OUT/f'receipt-{index:02d}.json').open('x') as saved:
        json.dump({'input':fixture,'receipt':receipt},saved)
    checked=checker.check(fixture['adjacency'],receipt,seconds=max(0,deadline-time.monotonic()))
    assert receipt['nodes']<=cap+1
    results.append({'fixture':{k:v for k,v in fixture.items() if k!='adjacency'},'receipt':receipt,'checked':checked})
(OUT/'results.json').write_text(json.dumps(results)+'\n')
out={'visited':len(results),'unvisited':len(inputs)-len(results),'seconds':time.monotonic()-start,
     'results':[dict(r['fixture'],status=r['receipt']['status'],nodes=r['receipt']['nodes'],**r['checked']) for r in results],
     'scope':'Only eight specified F0 high inputs; no whole F0/H7/Lean/global exclusion.'}
(OUT/'summary.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
