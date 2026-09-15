"""Independent full host-export join and residual negative endpoint audit.

Usage: python3 audit_residual.py TARGET F_INDEX OUTPUT_DIRECTORY
Does not import any producer code or run a graph search.
"""
import ctypes,gzip,hashlib,itertools,json,sys,time
from collections import Counter
from pathlib import Path

P=Path(sys.argv[1]);F=int(sys.argv[2]);O=Path(sys.argv[3]);O.mkdir(parents=True,exist_ok=True)
ROOT=Path('/Users/rwalters/GitHub/lean-genius/.codex/worktrees/erdos85-sol2-integration/research/problems/erdos-85-wip-01')
def read(p):return json.loads(p.read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def stream(paths):
    for p in paths:
        with gzip.open(p,'rt') as f:
            for line in f:yield json.loads(line)

start=time.monotonic()
host=read(P/'hosts/results.json');result=read(P/'residual/results.json');launch=read(P/'residual/launch.json')
assert host['unvisited']==0 and set(host['counts'])=={'COMPLETE'}
for name,h in read(P/'host-pins.json').items():assert sha(P/name)==h
assert launch['host_pins_sha256']==sha(P/'host-pins.json')
assert launch['source_export_sha256']==sha(P/'residual/source-leaves.jsonl.gz')
high=read(P/'high-results.json')['results'];hl=read(P/'high-launch.json');source=Path(hl['source_path'])
for name,h in hl['source_pins'].items():assert sha(source/name)==h
reps=read(source/'results.json')['representatives'];done=read(source/'completion-results.json')['results']
extra=Path(hl['complement_path'])
for name,h in hl['complement_pins'].items():assert sha(extra/name)==h
mapping=read(extra/'coverage-map.json');source_records={}
for key,meta in mapping['sources'].items():
    path=Path(meta['path']);assert sha(path)==meta['sha256'];source_records[key]=read(path)['results']
records=[]
for row in mapping['rows']:
    if row['F_index']!=F:continue
    rr=source_records[row['origin']][row['record_index']]
    assert rr['source_index']==row['source_index'] and rr['status']==row['status']=='COMPLETE' and rr['count']==row['saved_graphs']
    records.append(rr)
assert all(r['status']=='COMPLETE' for r in records)
assert {r['source_index'] for r in records}=={i for i,r in enumerate(reps) if r['F_index']==F}
solutions={r['source_index']:r['solutions'] for r in records}
keys=[(r['case_index'],pi) for r in high for pi in range(len(r['pairings']))]
libpath=ROOT/'q7_h7_a7_f9_closure/review/row-verifier/rows.dylib'
assert sha(libpath)=='cabf8dbf14dcfed235c764f836bc9b369e9bbac48050da0a0bc4eacb8cf87a4b'
lib=ctypes.CDLL(str(libpath));U=ctypes.c_uint64
lib.enumerate_rows.argtypes=[ctypes.POINTER(U),ctypes.c_int,ctypes.POINTER(U),ctypes.POINTER(U)]
lib.enumerate_rows.restype=ctypes.c_int
buf=(U*1024)();ops=U()
pinpaths=[P/'host-pins.json',P/'high-results.json',P/'residual/results.json',P/'residual/source-leaves.jsonl.gz']+[P/'residual'/n for n in result['receipt_shards']]
pins={str(p):sha(p) for p in pinpaths}
with (O/'launch.json').open('x') as f:json.dump({'seconds_cap':90,'pins':pins},f,indent=2)
export=iter(stream([P/'residual/source-leaves.jsonl.gz']))
receipts=iter(stream([P/'residual'/n for n in result['receipt_shards']]))
current=next(receipts,None);seen=[];frontier=[];retained=[];counts=Counter()
leaves=visited=domains=nrows=events=removals=0
for hostrow in stream([P/'hosts'/n for n in host['receipt_shards']]):
    assert time.monotonic()-start<90
    ci,pi=hostrow['case_index'],hostrow['pairing_index'];seen.append((ci,pi))
    assert hostrow['receipt']['status']=='COMPLETE'
    hs=hostrow['receipt']['solutions']
    if not hs:continue
    e=next(export)
    assert (e['case_index'],e['pairing_index'])==(ci,pi)
    assert all(len(row)==7 and all(m>=0 and m<1<<42 and m%(1<<21)==0 for m in row) for row in hs)
    assert e['hosts']==[[m>>21 for m in row] for row in hs]
    leaves+=len(hs)
    if current is None:
        frontier.extend([ci,pi,j] for j in range(len(hs)));continue
    assert (current['case_index'],current['pairing_index'])==(ci,pi)
    rr=current['receipts'];assert len(rr)<=len(hs)
    h=high[ci];rep=reps[h['source_index']];assert rep['F_index']==F
    base=[0]*49
    def add(a,b):base[a]|=1<<b;base[b]|=1<<a
    def ren(a):return a+42 if a<7 else a
    for a,b in rep['F_edges']+solutions[h['source_index']][h['singleton_index']]:add(ren(a),ren(b))
    for s,es in enumerate(rep['singleton_hosts'],7):
        for empty in es:add(s,empty+42)
    for j,(a,b) in enumerate(itertools.combinations(range(7),2),21):add(j,a);add(j,b)
    for hi,d in enumerate(h['pairings'][pi]):add(hi,14+hi);add(hi,7+d)
    for li,r in enumerate(rr):
        status=r['status'];counts[status]+=1;visited+=1
        if status in ('ARC_FEASIBLE','UNKNOWN'):
            retained.append([ci,pi,li,status]);continue
        assert status in ('INFEASIBLE_ROW','INFEASIBLE_ARC')
        g=base[:]
        for empty,m in enumerate(e['hosts'][li],42):
            g[empty]|=m<<21
            for j in range(21):
                if m>>j&1:g[j+21]|=1<<empty
        a=(U*49)(*g)
        def rows(u):
            global domains,nrows
            assert u in range(7,42)
            n=lib.enumerate_rows(a,u,buf,ctypes.byref(ops));assert 0<=n<=1024
            ans=set(buf[:n]);assert len(ans)==n
            domains+=1;nrows+=n;return ans
        if status=='INFEASIBLE_ROW':assert not rows(r['empty_vertex'])
        else:
            D={u:rows(u) for u in range(7,42)}
            assert set(map(int,r['initial']))==set(D) and all(D.values())
            for u in D:assert set(r['initial'][str(u)])==D[u] and len(r['initial'][str(u)])==len(D[u])
            for ev in r['events']:
                u,v,rm=ev['vertex'],ev['against'],ev['removed']
                assert u in D and v in D and u!=v and rm and len(set(rm))==len(rm) and set(rm)<=D[u]
                for row in rm:
                    assert not any(((row>>v)&1)==((other>>u)&1) and ((g[u]|row)&(g[v]|other)).bit_count()<=1 for other in D[v])
                D[u].difference_update(rm);events+=1;removals+=len(rm)
            assert not D[r['empty_vertex']]
    current=next(receipts,None)
    if len(rr)<len(hs):
        frontier.extend([ci,pi,j] for j in range(len(rr),len(hs)))
        assert current is None
assert next(export,None) is None and current is None and seen==keys
assert leaves==host['surviving_host_leaves_complete']==result['total']
assert visited==result['visited'] and len(frontier)==result['unvisited']
assert dict(counts)==result['counts'] and retained==result['retained']
for p,h in pins.items():assert sha(Path(p))==h
out={'status':'PASS_SOURCE_JOIN_AND_NEGATIVE_ENDPOINTS','F_index':F,'host_inputs':len(keys),'leaves':leaves,
     'visited':visited,'unvisited':len(frontier),'counts':dict(counts),'domains':domains,'rows':nrows,
     'arc_events':events,'removed_rows':removals,'seconds':time.monotonic()-start,
     'whole_negative_cover':not frontier and not retained,
     'scope':'No Lean kernel or arbitrary CNF UNSAT claim. Whole-shape exclusion also requires reviewed upstream source coverage.'}
(O/'result.json').write_text(json.dumps(out,indent=2)+'\n')
(O/'unvisited.json').write_text(json.dumps(frontier)+'\n');print(json.dumps(out))
