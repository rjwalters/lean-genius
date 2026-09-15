"""Independently regenerate negative row domains and check every arc removal."""
import collections
import ctypes
import gzip
import hashlib
import itertools
import json
import time
from pathlib import Path
from inputs import load,OLD
OUT=Path(__file__).parent
ROOT=Path('/Users/rwalters/GitHub/lean-genius/.codex/worktrees/erdos85-sol2-integration/research/problems/erdos-85-wip-01')

P=OUT/'residual'
REF=ROOT/'q7_h7_a7_f9_closure/review/row-verifier'
lib=ctypes.CDLL(str(REF/'rows.dylib'))
U=ctypes.c_uint64
lib.enumerate_rows.argtypes=[ctypes.POINTER(U),ctypes.c_int,ctypes.POINTER(U),ctypes.POINTER(U)]
lib.enumerate_rows.restype=ctypes.c_int
buffer=(U*1024)();nodes=U()
cover,cases,high=load()
result=json.loads((P/'results.json').read_text())
launch=json.loads((P/'launch.json').read_text())
assert hashlib.sha256((P/'source-leaves.jsonl.gz').read_bytes()).hexdigest()==launch['source_export_sha256']
pins={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in [REF/'rows.cpp',REF/'rows.dylib',OLD/'high-results.json',P/'source-leaves.jsonl.gz',P/'results.json']+[P/name for name in result['receipt_shards']]}
with (P/'verification-launch.json').open('x') as f: json.dump({'aggregate_seconds':120,'input_pins':pins},f,indent=2)
start=time.monotonic();deadline=start+120
counts=collections.Counter();visited=ndom=nrows=batches=removedcount=0
active=list(range(7,42));retained=[]

def given_high(ci,pi):
    g=[0]*49
    def add(u,v): g[u]|=1<<v;g[v]|=1<<u
    def ren(v): return v+42 if v<7 else v
    si,sj,es=cases[ci];rep=cover['representatives'][si]
    for u,v in rep['F_edges']+es:add(ren(u),ren(v))
    for s,hs in enumerate(rep['singleton_hosts'],7):
        for e in hs:add(s,42+e)
    for p,(u,v) in enumerate(itertools.combinations(range(7),2),21): add(p,u);add(p,v)
    for h,d in enumerate(high[ci]['pairings'][pi]): add(h,14+h);add(h,7+d)
    return g

def groups():
    for name in result['receipt_shards']:
        with gzip.open(P/name,'rt') as source:
            for line in source: yield json.loads(line)

# Exact stronger host-export join, separate from residual endpoints.
host_result=json.loads((OUT/'results.json').read_text())
with gzip.open(P/'source-leaves.jsonl.gz','rt') as export:
    total=0
    for name in host_result['receipt_shards']:
        for line in gzip.open(OUT/name,'rt'):
            host=json.loads(line);solutions=host['receipt']['solutions']
            assert host['receipt']['status']=='COMPLETE'
            if not solutions:continue
            item=json.loads(next(export))
            assert (item['case_index'],item['pairing_index'])==(host['case_index'],host['pairing_index'])
            assert item['hosts']==[[m>>21 for m in row] for row in solutions]
            total+=len(solutions)
    assert next(export,None) is None and total==3012
with gzip.open(P/'source-leaves.jsonl.gz','rt') as source:
    for record in groups():
        expected=json.loads(next(source))
        ci,pi=record['case_index'],record['pairing_index']
        assert (ci,pi)==(expected['case_index'],expected['pairing_index'])
        assert len(record['receipts'])<=len(expected['hosts'])
        base=given_high(ci,pi)
        for li,receipt in enumerate(record['receipts']):
            assert time.monotonic()<deadline,'Independent verification capped; producer remains frozen'
            g=base[:]
            for e,mask in enumerate(expected['hosts'][li],42):
                mask<<=21;g[e]|=mask
                while mask:
                    bit=mask&-mask;mask-=bit;g[bit.bit_length()-1]|=1<<e
            a=(U*49)(*g)
            def rows(u):
                global ndom,nrows
                assert u in active
                n=lib.enumerate_rows(a,u,buffer,ctypes.byref(nodes))
                assert 0<=n<=1024
                answer=set(buffer[:n]);assert len(answer)==n
                ndom+=1;nrows+=n
                return answer
            status=receipt['status'];counts[status]+=1;visited+=1
            before=nodes.value
            if status=='INFEASIBLE_ROW': assert not rows(receipt['empty_vertex'])
            elif status=='INFEASIBLE_ARC':
                D={u:rows(u) for u in active}
                assert all(D.values()) and set(map(int,receipt['initial']))==set(active)
                for u in active: assert len(receipt['initial'][str(u)])==len(D[u]) and set(receipt['initial'][str(u)])==D[u]
                for event in receipt['events']:
                    u,v=event['vertex'],event['against'];rm=event['removed']
                    assert u in D and v in D and u!=v and rm and len(set(rm))==len(rm) and set(rm)<=D[u]
                    for row in rm:
                        assert all(bool(row>>v&1)!=bool(other>>u&1) or ((g[u]|row)&(g[v]|other)).bit_count()>1 for other in D[v])
                        removedcount+=1
                    D[u]-=set(rm);batches+=1
                assert receipt['empty_vertex'] in D and not D[receipt['empty_vertex']]
            else:
                assert status in ('ARC_FEASIBLE','UNKNOWN')
                retained.append([ci,pi,li,status])
            assert nodes.value-before<=100000
        if len(record['receipts'])<len(expected['hosts']):
            assert visited==result['visited']
    if result['unvisited']==0: assert next(source,None) is None
assert visited==result['visited'] and dict(counts)==result['counts'] and retained==result['retained']
for name,h in pins.items():
    from pathlib import Path
    assert hashlib.sha256(Path(name).read_bytes()).hexdigest()==h
summary=dict(status='PASS_NEGATIVE_RECEIPTS',visited=visited,unvisited=result['unvisited'],counts=dict(counts),
             retained=len(retained),domains=ndom,rows=nrows,arc_batches=batches,failed_support_rows=removedcount,
             independent_subset_nodes=nodes.value,seconds=time.monotonic()-start,
             scope='Exact exported source order, all negative row endpoints and arc removal events. Positive/UNKNOWN not promoted; host export provenance requires source review.')
(P/'verification.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary))
