"""Exact old-negative/calibration/new-queue join; no endpoint or solver run."""
import gzip,hashlib,json,time
from collections import Counter
from pathlib import Path
P=Path('/Users/rwalters/lean-genius-h7-f0-pairrow-sol2-20260915')
OLD=Path('/Users/rwalters/lean-genius-h7-f0-sol1-20260915')
CAL=Path('/Users/rwalters/lean-genius-h7-host-pairrow-sol2-20260915')
O=Path(__file__).parent
def read(p):return json.loads(p.read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def records(paths):
    for p in paths:
        with gzip.open(p,'rt') as f:
            for line in f:yield json.loads(line)
start=time.monotonic();launch=read(P/'launch.json');result=read(P/'results.json')
for n,h in launch['source_pins'].items():
    path=Path(n);assert sha(path)==h
    for source,digest in read(path).items():assert sha(path.parent/source)==digest
assert sha(P/'run.py')==launch['driver_sha256'] and sha(P/'inputs.py')==launch['inputs_sha256']
assert sha(CAL/'cached/hosts.dylib')==launch['native_sha256']
old_negative=set()
for r in records([OLD/n for n in read(OLD/'host-results.json')['shards']]):
    if r['receipt']['status']=='COMPLETE' and not r['receipt']['solutions']:
        k=r['case_index'],r['pairing_index'];assert k not in old_negative;old_negative.add(k)
assert len(old_negative)==60
cal_negative=set()
for r in read(CAL/'calibration-450k/results.json'):
    assert r['receipt']['status']=='COMPLETE' and not r['receipt']['solutions']
    k=r['fixture']['case_index'],r['fixture']['pairing_index'];assert k not in cal_negative;cal_negative.add(k)
assert len(cal_negative)==8 and not old_negative&cal_negative
known=old_negative|cal_negative
expected_covered=[{'case_index':ci,'pairing_index':pi,'evidence':'review2656' if (ci,pi) in old_negative else 'review2672'} for ci,pi in sorted(known)]
assert read(P/'covered-inputs.json')==expected_covered
high=read(OLD/'high-results.json')['results']
full=[(r['case_index'],pi) for r in high for pi in range(len(r['pairings']))]
assert len(full)==len(set(full))==18408
queue=[k for k in full if k not in known];assert len(queue)==18340
assert read(P/'queue.json')==[list(k) for k in queue]
files=[P/'results.json',P/'queue.json',P/'covered-inputs.json']+[P/n for n in result['receipt_shards']]
pins={str(p):sha(p) for p in files}
with (O/'join-launch.json').open('x') as f:json.dump({'seconds_cap':90,'inputs':pins},f,indent=2)
counts=Counter();seen=[];unknown=[];negative=leaves=pair=single=nodes=0;positive=[]
for r in records([P/n for n in result['receipt_shards']]):
    assert time.monotonic()-start<90
    ci,pi=r['case_index'],r['pairing_index'];assert (ci,pi)==queue[len(seen)];seen.append((ci,pi))
    cert=r['receipt'];status=cert['status'];assert status in ('COMPLETE','UNKNOWN');counts[status]+=1;nodes+=cert['nodes']
    if status=='UNKNOWN':unknown.append([ci,pi]);continue
    assert cert['nodes']<=450000
    negative+=not cert['solutions'];leaves+=len(cert['solutions'])
    pair+=sum('pair_vertex' in p for p in cert['prunes']);single+=sum('singleton' in p for p in cert['prunes'])
    assert all(('pair_vertex' in p)!=('singleton' in p) for p in cert['prunes'])
    if cert['solutions']:positive.append([ci,pi,len(cert['solutions'])])
assert dict(counts)==result['counts'] and len(seen)==result['visited']
assert len(queue)-len(seen)==result['unvisited'] and unknown==result['unknown']
assert (negative,leaves,pair,single,nodes)==(result['negative_high_inputs'],result['surviving_host_leaves'],result['pair_prunes_complete'],result['singleton_prunes_complete'],result['nodes'])
assert sum((P/n).stat().st_size for n in result['receipt_shards'])==result['artifact_bytes']<=250000000
assert all((P/n).stat().st_size<50000000 for n in result['receipt_shards'])
for n,h in pins.items():assert sha(Path(n))==h
out={'status':'PASS_EXACT_REUSE_AND_QUEUE_JOIN','old_negative':60,'calibration_negative':8,'full_high_inputs':18408,
     'new_visited':len(seen),'new_unvisited':len(queue)-len(seen),'counts':dict(counts),'new_negative':negative,
     'leaves':leaves,'pair_prunes':pair,'singleton_prunes':single,'positive_inputs':positive,'seconds':time.monotonic()-start,
     'whole_negative_cover':not unknown and len(seen)==len(queue) and leaves==0,
     'scope':'Input coverage and receipt accounting only; negative endpoint truth requires the separate reviewed verifier.'}
(O/'join-result.json').write_text(json.dumps(out,indent=2)+'\n');print({k:v for k,v in out.items() if k!='positive_inputs'})
