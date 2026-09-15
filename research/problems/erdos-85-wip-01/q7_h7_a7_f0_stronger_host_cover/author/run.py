"""One complete-queue attempt using the reviewed stronger host predicate."""
import collections
import gzip
import hashlib
import importlib.util
import json
import sqlite3
import time
from pathlib import Path
from inputs import OLD,load,graph

P=Path(__file__).parent
N=Path('/Users/rwalters/lean-genius-h7-host-pairrow-sol2-20260915')
CAL=N/'calibration-450k'
db=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True)
reviews={}
for rid in [2116,2654,2656,2669,2670,2672]:
    r=db.execute('select status,resolution from review_requests where id=?',(rid,)).fetchone()
    assert r and r[0]=='resolved' and r[1].startswith('PASS'),(rid,r)
    reviews[rid]=r
pins={}
for root,pinfile in [(OLD,'pins.json'),(N,'pins.json'),(N,'calibration-pins.json')]:
    manifest=json.loads((root/pinfile).read_text())
    for name,h in manifest.items():assert hashlib.sha256((root/name).read_bytes()).hexdigest()==h
    pins[str(root/pinfile)]=hashlib.sha256((root/pinfile).read_bytes()).hexdigest()
cover,cases,high=load()
full=[(ci,pi) for ci,r in enumerate(high) for pi in range(len(r['pairings']))]
old=json.loads((OLD/'host-results.json').read_text())
covered={};oldkeys=[]
for name in old['shards']:
    for line in gzip.open(OLD/name,'rt'):
        r=json.loads(line);key=r['case_index'],r['pairing_index'];oldkeys.append(key)
        if r['receipt']['status']=='COMPLETE' and not r['receipt']['solutions']:covered[key]='review2656'
assert oldkeys==full[:old['visited']] and len(covered)==60
cal=json.loads((CAL/'results.json').read_text())
assert len(cal)==8
for r in cal:
    assert r['receipt']['status']=='COMPLETE' and not r['receipt']['solutions'] and r['checked']['coverage_proved']
    key=r['fixture']['case_index'],r['fixture']['pairing_index']
    assert key not in covered;covered[key]='review2672'
assert len(covered)==68 and set(covered)<=set(full)
queue=[key for key in full if key not in covered]
assert len(queue)==18340
(P/'covered-inputs.json').write_text(json.dumps([{'case_index':ci,'pairing_index':pi,'evidence':ref} for (ci,pi),ref in sorted(covered.items())],indent=2)+'\n')
(P/'queue.json').write_text(json.dumps(queue)+'\n')
spec=importlib.util.spec_from_file_location('reviewed_cached_host',N/'cached/api.py')
api=importlib.util.module_from_spec(spec);spec.loader.exec_module(api)
with (P/'launch.json').open('x') as f:
    json.dump({'total_high_inputs':18408,'covered_before':68,'queue':len(queue),'max_nodes':450000,
               'aggregate_seconds':240,'shard_byte_cap':50000000,'artifact_byte_cap':250000000,
               'reviews':reviews,'source_pins':pins,'native_sha256':hashlib.sha256((N/'cached/hosts.dylib').read_bytes()).hexdigest(),
               'driver_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
               'inputs_sha256':hashlib.sha256((P/'inputs.py').read_bytes()).hexdigest()},f,indent=2)
start=time.monotonic();deadline=start+240
counts=collections.Counter();visited=negative=leaves=pair_prunes=singleton_prunes=nodes=0
shards=[];stream=None;size=allsize=0;unknown=[];stop=None;unsaved=0
for ci,pi in queue:
    remaining=deadline-time.monotonic()
    if remaining<=0:stop='AGGREGATE_CAP';break
    receipt=api.enumerate_hosts(graph(cover,cases,high,ci,pi),max_nodes=450000,seconds=remaining)
    assert receipt['status'] in ('COMPLETE','UNKNOWN'),(ci,pi,receipt)
    record={'case_index':ci,'pairing_index':pi,'receipt':receipt}
    blob=gzip.compress((json.dumps(record,separators=(',',':'))+'\n').encode(),mtime=0)
    assert len(blob)<50000000
    if allsize+len(blob)>250000000:stop='ARTIFACT_CAP';unsaved=1;break
    if stream is None or size+len(blob)>50000000:
        if stream:stream.close()
        name=f'receipts-{len(shards):03d}.jsonl.gz';shards.append(name);stream=(P/name).open('xb');size=0
    stream.write(blob);size+=len(blob);allsize+=len(blob)
    visited+=1;counts[receipt['status']]+=1;nodes+=receipt['nodes']
    if receipt['status']=='UNKNOWN':unknown.append([ci,pi])
    else:
        negative+=not receipt['solutions'];leaves+=len(receipt['solutions'])
        pair_prunes+=sum('pair_vertex' in r for r in receipt['prunes'])
        singleton_prunes+=sum('singleton' in r for r in receipt['prunes'])
if stream:stream.close()
result={'total_high_inputs':18408,'covered_before':68,'queue':len(queue),'visited':visited,'unvisited':len(queue)-visited,
        'counts':dict(counts),'negative_high_inputs':negative,'surviving_host_leaves':leaves,
        'pair_prunes_complete':pair_prunes,'singleton_prunes_complete':singleton_prunes,'nodes':nodes,
        'unknown':unknown,'receipt_shards':shards,'artifact_bytes':allsize,'computed_not_saved':unsaved,
        'stop':stop,'seconds':time.monotonic()-start,'scope':'Necessary stronger host cover; unresolved/retained cases require further evidence.'}
(P/'results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='unknown'},indent=2))
