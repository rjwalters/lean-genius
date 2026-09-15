"""One bounded finishing slice on the frozen F2 residual frontier."""
import array
import collections
import ctypes
import gzip
import hashlib
import json
import sqlite3
import time
from pathlib import Path
from highs import ROOT, OUT, inputs, graph

API = ROOT/'q7_h7_a7_f9_closure/author'
P = OUT/'finish'
P.mkdir(exist_ok=True)
assert not (P/'launch.json').exists(), 'No overwrite or retry'
db=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True)
premises={}
for rid in (2111,2117,2655,2657,2658):
    r=db.execute('select status,resolution from review_requests where id=?',(rid,)).fetchone()
    assert r and r[0]=='resolved' and r[1].startswith('PASS'),(rid,r)
    premises[rid]=r
hostpins=json.loads((OUT/'host-pins.json').read_text())
for name,h in hostpins.items(): assert hashlib.sha256((OUT/name).read_bytes()).hexdigest()==h
api_pins=json.loads((API/'pins.json').read_text())
api_pins={name:api_pins[name] for name in ('batch.cpp','batch.dylib','filter.cpp')}
for name,h in api_pins.items(): assert hashlib.sha256((API/name).read_bytes()).hexdigest()==h
cover,cases=inputs()
high=json.loads((OUT/'high-results.json').read_text())
host=json.loads((OUT/'hosts/results.json').read_text())
assert host['unvisited']==0 and host['counts']=={'COMPLETE':24136}
total=host['surviving_host_leaves_complete']
assert total==785408

# Select exactly the previously unvisited suffix plus the last wall-cut leaf.
prior=json.loads((OUT/'residual/results.json').read_text())
assert prior['counts']=={'INFEASIBLE_ROW':705051,'INFEASIBLE_ARC':824,'UNKNOWN':1}
assert prior['visited']==705876 and prior['unvisited']==79532
assert prior['retained']==[[3710,1,9,'UNKNOWN']]
for name,h in json.loads((OUT/'residual-pins.json').read_text()).items():
    assert hashlib.sha256((OUT/name).read_bytes()).hexdigest()==h
cutoff=prior['visited']-1
export=P/'source-leaves.jsonl.gz'
offset=leaves=0
with gzip.open(export,'xt') as out:
    for line in gzip.open(OUT/'residual/source-leaves.jsonl.gz','rt'):
        group=json.loads(line);n=len(group['hosts']);first=max(0,cutoff-offset)
        if first<n:
            selected=dict(group,first_leaf=first,hosts=group['hosts'][first:])
            out.write(json.dumps(selected,separators=(',',':'))+'\n')
            leaves+=n-first
        offset+=n
assert offset==785408 and leaves==79533
total=leaves
export_sha=hashlib.sha256(export.read_bytes()).hexdigest()
lib=ctypes.CDLL(str(API/'batch.dylib'))
lib.native_now.restype=ctypes.c_double
assert abs(lib.native_now()-time.monotonic())<0.1
lib.batch_check.argtypes=[ctypes.POINTER(ctypes.c_uint64),ctypes.POINTER(ctypes.c_uint32),ctypes.c_int,ctypes.c_int,ctypes.c_double]
lib.batch_check.restype=ctypes.c_char_p
with (P/'launch.json').open('x') as f:
    json.dump(dict(total=total,max_nodes=100000,aggregate_seconds=30,shard_byte_cap=50000000,
                   artifact_byte_cap=150000000,premises=premises,api_path=str(API),api_pins=api_pins,
                   host_pins_sha256=hashlib.sha256((OUT/'host-pins.json').read_bytes()).hexdigest(),
                   prior_residual_pins_sha256=hashlib.sha256((OUT/'residual-pins.json').read_bytes()).hexdigest(),
                   source_export_sha256=export_sha,driver_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()),f,indent=2)
start=time.monotonic();deadline=start+30
counts=collections.Counter();visited=nodes=allsize=size=0
retained=[];shards=[];stream=None;stop=None;discarded_at_cap=0
lastci=None;base=None
with gzip.open(export,'rt') as source:
    for line in source:
        if time.monotonic()>=deadline: stop='AGGREGATE_CAP';break
        group=json.loads(line);ci,pi=group['case_index'],group['pairing_index']
        row=high['results'][ci]
        if lastci!=ci:
            assert (row['source_index'],row['singleton_index'])==cases[ci][:2]
            base=(ctypes.c_uint64*21)(*[sum(1<<v for v in ns) for ns in graph(cover,cases[ci])])
            lastci=ci
        flat=array.array('I',(v for hs in group['hosts'] for part in (row['pairings'][pi],hs) for v in part))
        assert flat.itemsize==4
        receipts=json.loads(lib.batch_check(base,(ctypes.c_uint32*len(flat)).from_buffer(flat),len(group['hosts']),100000,deadline))
        assert len(receipts)<=len(group['hosts'])
        blob=gzip.compress((json.dumps({'case_index':ci,'pairing_index':pi,'first_leaf':group['first_leaf'],'receipts':receipts},separators=(',',':'))+'\n').encode(),mtime=0)
        assert len(blob)<50000000
        if allsize+len(blob)>150000000:
            stop='ARTIFACT_CAP';discarded_at_cap=len(receipts);break
        for li,r in enumerate(receipts):
            assert r['status'] in ('INFEASIBLE_ROW','INFEASIBLE_ARC','ARC_FEASIBLE','UNKNOWN'),(ci,pi,li,r)
            counts[r['status']]+=1;nodes+=r['nodes'];visited+=1
            if r['status'] in ('ARC_FEASIBLE','UNKNOWN'): retained.append([ci,pi,group['first_leaf']+li,r['status']])
        if stream is None or size+len(blob)>50000000:
            if stream: stream.close()
            name=f'receipts-{len(shards):03d}.jsonl.gz'
            shards.append(name);stream=(P/name).open('xb');size=0
        stream.write(blob);size+=len(blob);allsize+=len(blob)
        if len(receipts)<len(group['hosts']): stop='AGGREGATE_CAP';break
        if allsize>=150000000: stop='ARTIFACT_CAP';break
if stream: stream.close()
result=dict(total=total,visited=visited,unvisited=total-visited,counts=dict(counts),nodes=nodes,
            retained=retained,receipt_shards=shards,artifact_bytes=allsize,seconds=time.monotonic()-start,stop=stop,
            computed_but_not_retained_at_artifact_cap=discarded_at_cap,
            scope='Necessary residual row and pairwise arc consistency only; positive or UNKNOWN leaves are not graph witnesses.')
(P/'results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='retained'},indent=2))
