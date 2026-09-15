"""One residual pass over the complete stronger F0 host cover."""
import array
import argparse
import collections
import ctypes
import gzip
import hashlib
import json
import sqlite3
import time
from pathlib import Path
from inputs import load,graph

P=Path(__file__).parent
OUT=P/'residual'
OUT.mkdir(exist_ok=True)
args=argparse.ArgumentParser();args.add_argument('--source-review',type=int,required=True);args=args.parse_args()
db=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True)
premises={}
for rid in [2111,2117,args.source_review]:
    r=db.execute('select status,resolution from review_requests where id=?',(rid,)).fetchone()
    assert r and r[0]=='resolved' and r[1].startswith('PASS'),(rid,r);premises[rid]=r
for name,h in json.loads((P/'host-pins.json').read_text()).items():assert hashlib.sha256((P/name).read_bytes()).hexdigest()==h
host=json.loads((P/'results.json').read_text())
assert host['counts']=={'COMPLETE':18340} and host['unvisited']==0 and host['surviving_host_leaves']==3012
API=Path('/Users/rwalters/GitHub/lean-genius/.codex/worktrees/erdos85-sol2-integration/research/problems/erdos-85-wip-01/q7_h7_a7_f9_closure/author')
pins=json.loads((API/'pins.json').read_text());pins={name:pins[name] for name in ['batch.cpp','batch.dylib','filter.cpp']}
for name,h in pins.items():assert hashlib.sha256((API/name).read_bytes()).hexdigest()==h
cover,cases,high=load();total=0
with gzip.open(OUT/'source-leaves.jsonl.gz','xt') as dest:
    for name in host['receipt_shards']:
        for line in gzip.open(P/name,'rt'):
            r=json.loads(line);assert r['receipt']['status']=='COMPLETE';hs=r['receipt']['solutions']
            if hs:
                assert all(len(row)==7 and all(mask&((1<<21)-1)==0 and mask>>42==0 for mask in row) for row in hs)
                dest.write(json.dumps({'case_index':r['case_index'],'pairing_index':r['pairing_index'],'hosts':[[m>>21 for m in row] for row in hs]},separators=(',',':'))+'\n')
                total+=len(hs)
assert total==3012
lib=ctypes.CDLL(str(API/'batch.dylib'));U,I=ctypes.c_uint64,ctypes.c_uint32
lib.native_now.restype=ctypes.c_double;assert abs(lib.native_now()-time.monotonic())<0.1
lib.batch_check.argtypes=[ctypes.POINTER(U),ctypes.POINTER(I),ctypes.c_int,ctypes.c_int,ctypes.c_double];lib.batch_check.restype=ctypes.c_char_p
with (OUT/'launch.json').open('x') as f:
    json.dump({'total':total,'aggregate_seconds':30,'max_nodes':100000,'api_path':str(API),'api_pins':pins,
               'source_export_sha256':hashlib.sha256((OUT/'source-leaves.jsonl.gz').read_bytes()).hexdigest(),
               'host_pins_sha256':hashlib.sha256((P/'host-pins.json').read_bytes()).hexdigest(),
               'premises':premises,'driver_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()},f,indent=2)
start=time.monotonic();deadline=start+30;visited=nodes=0;counts=collections.Counter();retained=[]
with gzip.open(OUT/'receipts-000.jsonl.gz','xt') as dest:
    for line in gzip.open(OUT/'source-leaves.jsonl.gz','rt'):
        if time.monotonic()>=deadline:break
        r=json.loads(line);ci,pi=r['case_index'],r['pairing_index']
        g=graph(cover,cases,high,ci,pi)
        def old(v):return v+42 if v<7 else v
        base=[]
        for u in range(21):
            base.append(sum(1<<v for v in range(21) if old(v) in g[old(u)]))
        flat=array.array('I',(x for row in r['hosts'] for part in (high[ci]['pairings'][pi],row) for x in part))
        assert flat.itemsize==4
        receipts=json.loads(lib.batch_check((U*21)(*base),(I*len(flat)).from_buffer(flat),len(r['hosts']),100000,deadline))
        assert len(receipts)<=len(r['hosts'])
        dest.write(json.dumps({'case_index':ci,'pairing_index':pi,'receipts':receipts},separators=(',',':'))+'\n')
        for li,receipt in enumerate(receipts):
            assert receipt['status'] in ('INFEASIBLE_ROW','INFEASIBLE_ARC','ARC_FEASIBLE','UNKNOWN'),receipt
            visited+=1;nodes+=receipt['nodes'];counts[receipt['status']]+=1
            if receipt['status'] in ('ARC_FEASIBLE','UNKNOWN'):retained.append([ci,pi,li,receipt['status']])
        if len(receipts)<len(r['hosts']):break
result={'total':total,'visited':visited,'unvisited':total-visited,'counts':dict(counts),'retained':retained,
        'nodes':nodes,'receipt_shards':['receipts-000.jsonl.gz'],'seconds':time.monotonic()-start,
        'scope':'Necessary residual row/arc conditions; positive/UNKNOWN are not graph witnesses.'}
(OUT/'results.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
