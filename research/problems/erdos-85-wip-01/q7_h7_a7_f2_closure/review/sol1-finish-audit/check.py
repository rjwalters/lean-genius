"""Independent exact finishing frontier join and negative endpoint check."""
import ctypes
import gzip
import hashlib
import itertools
import json
import time
from collections import Counter
from pathlib import Path

SRC=Path('/Users/rwalters/lean-genius-h7-f2-sol2-20260915')
OLD=Path('/Users/rwalters/lean-genius-h7-f2-review-sol1-20260915')
OUT=Path(__file__).parent
ROOT=Path('/Users/rwalters/GitHub/lean-genius/.codex/worktrees/erdos85-sol2-integration/research/problems/erdos-85-wip-01')
def read(p):return json.loads(p.read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def stream(paths):
    for p in paths:
        with gzip.open(p,'rt') as f:
            for line in f:yield json.loads(line)

def run():
    start=time.monotonic()
    pins=read(SRC/'finish-pins.json')
    for n,h in pins.items():assert sha(SRC/n)==h,n
    with (OUT/'launch.json').open('x') as f:
        json.dump({'seconds_cap':60,'finish_pins_sha256':sha(SRC/'finish-pins.json')},f)
    wanted=[r[:3] for r in read(SRC/'residual/results.json')['retained']]+read(OLD/'unvisited.json')
    assert len(wanted)==79533 and len({tuple(x) for x in wanted})==79533
    wanted_set={tuple(x) for x in wanted}
    finished=list(stream([SRC/'finish/source-leaves.jsonl.gz']))
    fi=iter(finished);selected=[];total=0
    for group in stream([SRC/'residual/source-leaves.jsonl.gz']):
        ci,pi=group['case_index'],group['pairing_index']
        indices=[i for i in range(len(group['hosts'])) if (ci,pi,i) in wanted_set]
        if not indices:continue
        f=next(fi)
        assert (f['case_index'],f['pairing_index'])==(ci,pi)
        assert indices==list(range(f['first_leaf'],len(group['hosts'])))
        assert f['hosts']==[group['hosts'][i] for i in indices]
        selected.extend([ci,pi,i] for i in indices)
    assert next(fi,None) is None and selected==wanted
    result=read(SRC/'finish/results.json')
    receipts=iter(stream([SRC/'finish'/n for n in result['receipt_shards']]))
    high=read(SRC/'high-results.json')['results']
    source=ROOT/'q7_h7_a7_noncycle_singleton_projection/author'
    reps=read(source/'results.json')['representatives']
    solutions={r['source_index']:r['solutions'] for r in read(source/'completion-results.json')['results'] if r['F_index']==2}
    libpath=ROOT/'q7_h7_a7_f9_closure/review/row-verifier/rows.dylib'
    lib=ctypes.CDLL(str(libpath));U=ctypes.c_uint64
    lib.enumerate_rows.argtypes=[ctypes.POINTER(U),ctypes.c_int,ctypes.POINTER(U),ctypes.POINTER(U)]
    lib.enumerate_rows.restype=ctypes.c_int
    buf=(U*1024)();ops=U();counts=Counter();domains=nrows=events=removals=0
    for f in finished:
        assert time.monotonic()-start<60
        r=next(receipts);ci,pi=f['case_index'],f['pairing_index']
        assert (r['case_index'],r['pairing_index'],r['first_leaf'])==(ci,pi,f['first_leaf'])
        assert len(r['receipts'])==len(f['hosts'])
        h=high[ci];rep=reps[h['source_index']];base=[0]*49
        def add(a,b):base[a]|=1<<b;base[b]|=1<<a
        def ren(a):return a+42 if a<7 else a
        for a,b in rep['F_edges']+solutions[h['source_index']][h['singleton_index']]:add(ren(a),ren(b))
        for s,es in enumerate(rep['singleton_hosts'],7):
            for e in es:add(s,e+42)
        for j,(a,b) in enumerate(itertools.combinations(range(7),2),21):add(j,a);add(j,b)
        for hi,d in enumerate(h['pairings'][pi]):add(hi,14+hi);add(hi,7+d)
        for hs,rr in zip(f['hosts'],r['receipts']):
            g=base[:]
            for e,m in enumerate(hs,42):
                g[e]|=m<<21
                for j in range(21):
                    if m>>j&1:g[j+21]|=1<<e
            a=(U*49)(*g)
            def rows(u):
                nonlocal domains,nrows
                assert u in range(7,42)
                n=lib.enumerate_rows(a,u,buf,ctypes.byref(ops));assert 0<=n<=1024
                ans=set(buf[:n]);assert len(ans)==n
                domains+=1;nrows+=n;return ans
            status=rr['status'];counts[status]+=1;total+=1
            if status=='INFEASIBLE_ROW':assert not rows(rr['empty_vertex'])
            else:
                assert status=='INFEASIBLE_ARC'
                D={u:rows(u) for u in range(7,42)}
                assert set(map(int,rr['initial']))==set(D) and all(D.values())
                for u in D:assert set(rr['initial'][str(u)])==D[u] and len(rr['initial'][str(u)])==len(D[u])
                for ev in rr['events']:
                    u,v,rm=ev['vertex'],ev['against'],ev['removed']
                    assert u in D and v in D and u!=v and rm and len(set(rm))==len(rm) and set(rm)<=D[u]
                    for row in rm:
                        assert not any(((row>>v)&1)==((other>>u)&1) and ((g[u]|row)&(g[v]|other)).bit_count()<=1 for other in D[v])
                    D[u].difference_update(rm);events+=1;removals+=len(rm)
                assert not D[rr['empty_vertex']]
    assert next(receipts,None) is None
    assert total==79533==result['visited'] and result['unvisited']==0 and not result['retained']
    assert dict(counts)==result['counts']
    for n,h in pins.items():assert sha(SRC/n)==h,n
    summary={'status':'PASS_EXACT_FINISH_AND_NEGATIVES','leaves':total,'counts':dict(counts),'domains':domains,
             'rows':nrows,'arc_events':events,'removed_rows':removals,'seconds':time.monotonic()-start,
             'row_library_sha256':sha(libpath),'combined_negative_host_leaves':705875+total,
             'scope':'Complete F2 host-leaf rejection conditional on reviewed upstream covers; no Lean/kernel closure.'}
    (OUT/'result.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary))

if __name__=='__main__':run()
