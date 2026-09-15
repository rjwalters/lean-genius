import collections,ctypes,gzip,hashlib,json,time
from pathlib import Path
P=Path('/Users/rwalters/lean-genius-h7-a6-f18-sol2-20260915');O=Path(__file__).parent
ROOT=Path('/Users/rwalters/GitHub/lean-genius/.codex/worktrees/erdos85-sol2-integration/research/problems/erdos-85-wip-01')
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def stream(paths):
    for p in paths:
        with gzip.open(p,'rt') as f:
            for line in f:yield json.loads(line)
l=read(P/'launch.json');res=read(P/'results.json');S=Path(l['source_path']);A=Path(l['api_path'])
assert sha(S/'pins.json')==l['source_pins_sha256'] and sha(A/'pins.json')==l['api_pins_sha256']
for root in (S,A):
    for n,h in read(root/'pins.json').items():assert sha(root/n)==h
assert l['driver_sha256']==sha(P/'run.py') and l['aggregate_seconds']==90 and l['max_nodes']==100000 and res['seconds']<90
assert (P/'input-survivors.json').read_bytes()==(S/'survivors.json').read_bytes()
paths=[P/'results.json',P/'launch.json',P/'input-survivors.json']+[P/n for n in res['shards']]
pins={str(p):sha(p) for p in paths}
with (O/'launch.json').open('x') as f:json.dump({'seconds_cap':120,'input_pins':pins},f,indent=2)
start=time.monotonic();inputs=list(stream([S/'inputs.jsonl.gz']));bases={r['global_index']:r for r in inputs};assert len(bases)==len(inputs)==30182
expected=read(S/'survivors.json');host=read(S/'results.json');assert host['counts']=={'COMPLETE':30182} and host['unvisited']==0 and len(expected)==331996
N=ROOT/'q7_h7_a6_f15_closure/source/row-verifier/rows.dylib';assert sha(N)=='cabf8dbf14dcfed235c764f836bc9b369e9bbac48050da0a0bc4eacb8cf87a4b'
U=ctypes.c_uint64;lib=ctypes.CDLL(str(N));lib.enumerate_rows.argtypes=[ctypes.POINTER(U),ctypes.c_int,ctypes.POINTER(U),ctypes.POINTER(U)];lib.enumerate_rows.restype=ctypes.c_int
buf=(U*1024)();ops=U();rr=iter(stream([P/n for n in res['shards']]));current=next(rr,None)
seen=[];allkeys=[];counts=collections.Counter();retained=[];ndom=nrows=events=removals=0
for index,h in enumerate(stream([S/n for n in host['shards']])):
    assert time.monotonic()-start<120
    gid=h['global_index'];assert gid==inputs[index]['global_index']
    assert h['receipt']['status']=='COMPLETE' and h['receipt']['empty_vertices']==list(range(42,49))
    for key in ('completion_index','singleton_index','colouring_index'):assert h[key]==bases[gid][key]
    hs=h['receipt']['solutions'];allkeys.extend([gid,j] for j in range(len(hs)))
    if not hs:continue
    assert current is not None and current['global_index']==gid
    receipts=current['receipts'];assert len(receipts)==len(hs)
    base=[sum(1<<v for v in ns) for ns in bases[gid]['neighbors']]
    for li,c in enumerate(receipts):
        seen.append([gid,li]);status=c['status'];counts[status]+=1
        if status in ('UNKNOWN','ARC_FEASIBLE'):retained.append([gid,li,status]);continue
        assert status in ('INFEASIBLE_ROW','INFEASIBLE_ARC')
        g=base[:]
        for e,m in enumerate(hs[li],42):
            assert m>=0 and m&((1<<21)-1)==0 and m>>42==0
            g[e]|=m
            for v in range(21,42):
                if m>>v&1:g[v]|=1<<e
        adj=(U*49)(*g)
        def rows(u):
            global ndom,nrows
            assert 7<=u<42
            n=lib.enumerate_rows(adj,u,buf,ctypes.byref(ops));assert 0<=n<=1024
            ans=set(buf[:n]);assert len(ans)==n;ndom+=1;nrows+=n;return ans
        if status=='INFEASIBLE_ROW':assert not rows(c['empty_vertex'])
        else:
            D={u:rows(u) for u in range(7,42)}
            assert set(map(int,c['initial']))==set(D) and all(D.values())
            for u in D:assert set(c['initial'][str(u)])==D[u] and len(c['initial'][str(u)])==len(D[u])
            for e in c['events']:
                u,v,removed=e['vertex'],e['against'],e['removed']
                assert u in D and v in D and u!=v and removed and len(removed)==len(set(removed)) and set(removed)<=D[u]
                for row in removed:
                    assert not any(((row>>v)&1)==((other>>u)&1) and ((g[u]|row)&(g[v]|other)).bit_count()<=1 for other in D[v])
                D[u].difference_update(removed);events+=1;removals+=len(removed)
            assert not D[c['empty_vertex']]
    current=next(rr,None)
assert current is None and allkeys==seen==expected
assert len(seen)==res['total']==res['visited']==331996 and res['unvisited']==0
assert dict(counts)==res['counts'] and retained==res['retained']
for n,h in pins.items():assert sha(Path(n))==h
out={'status':'PASS_EXACT_HOST_JOIN_AND_NEGATIVE_ENDPOINTS','host_inputs':30182,'leaves':len(seen),'counts':dict(counts),'domains':ndom,'rows':nrows,'arc_events':events,'removed_rows':removals,'whole_negative_cover':not retained,'seconds':time.monotonic()-start,'scope':'Exact accepted2133 host/input/survivor join and independent complete row/arc checks. Upstream source/high/quotient coverage remains a reviewed premise; no arbitrary CNF UNSAT, Lean or global theorem.'}
(O/'REVIEW.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
