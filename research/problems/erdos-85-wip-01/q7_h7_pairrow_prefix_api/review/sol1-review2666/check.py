"""Fresh native build, distinct F3 fixtures, every prefix depth, relabellings."""
import ctypes,gzip,hashlib,importlib.util,itertools,json,time
from pathlib import Path
P=Path('/Users/rwalters/lean-genius-h7-pairrow-prefix-sol2-20260915');O=Path(__file__).parent
S=Path('/Users/rwalters/lean-genius-h7-f3-sol1-20260915')
ROOT=Path('/Users/rwalters/GitHub/lean-genius/.codex/worktrees/erdos85-sol2-integration/research/problems/erdos-85-wip-01')
def read(p):return json.loads(p.read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def module(name,path):
    spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
for n,h in read(P/'pins.json').items():assert sha(P/n)==h
for n,h in read(P/'PROVENANCE.json')['input_pins'].items():assert sha(Path(n))==h
for n,h in read(S/'host-pins.json').items():assert sha(S/n)==h
ref=module('prefix_reference',P/'reference.py');api=module('prefix_api',P/'api.py')
cv=module('host_cv',ROOT/'q7_h7_a7_f9_host_cover/author/cover_reference.py')
lib=ctypes.CDLL(str(O/'rebuilt.dylib'));U=ctypes.c_uint64
lib.pair_rows.argtypes=[ctypes.POINTER(U),ctypes.c_int,ctypes.c_int,ctypes.c_int,ctypes.c_double];lib.pair_rows.restype=ctypes.c_char_p
old=ctypes.CDLL(str(ROOT/'q7_h7_a7_f9_closure/review/row-verifier/rows.dylib'))
old.enumerate_rows.argtypes=[ctypes.POINTER(U),ctypes.c_int,ctypes.POINTER(U),ctypes.POINTER(U)];old.enumerate_rows.restype=ctypes.c_int
def arr(g):return (U*49)(*[sum(1<<v for v in ns) for ns in g])
source=Path(read(S/'high-launch.json')['source_path']);reps=read(source/'results.json')['representatives']
sols={r['source_index']:r['solutions'] for r in read(source/'completion-results.json')['results'] if r['F_index']==3}
high=read(S/'high-results.json')['results'];fixtures=[];ix=0
for shard in read(S/'hosts/results.json')['receipt_shards']:
    with gzip.open(S/'hosts'/shard,'rt') as f:
        for line in f:
            r=json.loads(line)
            if ix in (17,5003,10007,20011) and r['receipt']['solutions']:fixtures.append(r)
            ix+=1
assert len(fixtures)>=3
permutation=[2,5,1,0,6,4,3]+list(range(20,6,-1))+list(range(41,20,-1))+list(range(48,41,-1))
assert sorted(permutation)==list(range(49))
start=time.monotonic();checks=positive=fullchecks=retained=0
buf=(U*1024)();nodes=U()
for fixture in fixtures:
    h=high[fixture['case_index']];r=reps[h['source_index']];base=[set() for _ in range(49)]
    def add(g,a,b):g[a].add(b);g[b].add(a)
    ren=lambda a:a+42 if a<7 else a
    for a,b in r['F_edges']+sols[h['source_index']][h['singleton_index']]:add(base,ren(a),ren(b))
    for s,es in enumerate(r['singleton_hosts'],7):
        for e in es:add(base,s,e+42)
    for p,(a,b) in enumerate(itertools.combinations(range(7),2),21):add(base,p,a);add(base,p,b)
    for hi,d in enumerate(h['pairings'][fixture['pairing_index']]):add(base,hi,14+hi);add(base,hi,7+d)
    cert=fixture['receipt'];chosen=cert['solutions'][-1];order=cert['order'];opts=cv.options(base,list(range(42,49)))
    def prefix(depth):
        g=[set(ns) for ns in base]
        for i in order[:depth]:
            for p in range(21,42):
                if chosen[i]>>p&1:add(g,42+i,p)
        return g
    def transform(g,perm):
        out=[set() for _ in range(49)]
        for u,ns in enumerate(g):out[perm[u]]={perm[v] for v in ns}
        return out
    for perm in (list(range(49)),permutation):
        full=transform(prefix(7),perm);final={}
        for p in range(21,42):
            u=perm[p];n=old.enumerate_rows(arr(full),u,buf,ctypes.byref(nodes));assert 0<=n<=1024
            final[u]=set(buf[:n])
        for depth in range(8):
            g=transform(prefix(depth),perm)
            for p in range(21,42):
                assert time.monotonic()-start<60
                u=perm[p];future=any(m>>p&1 for i in order[depth:] for m in opts[i])
                assert future==ref.future_possible(opts,order,depth,p)
                native=json.loads(lib.pair_rows(arr(g),u,int(future),100000,1))
                packaged=api.rows(g,u,future)
                assert native['status']==packaged['status']=='COMPLETE'
                expected=ref.rows(g,u,future);actual=set(native['rows'])
                assert len(actual)==len(native['rows']) and actual==set(packaged['rows'])==expected
                assert final[u]<=actual
                checks+=1;positive+=bool(actual);retained+=len(final[u])
                if depth==7:assert actual==final[u];fullchecks+=1
        assert json.loads(lib.pair_rows(arr(base),21,1,0,1))['status']=='UNKNOWN'
        assert json.loads(lib.pair_rows(arr(base),21,1,100000,0))['status']=='UNKNOWN'
        for bad_u,bad_f in ((2**32+21,True),(21,0.5),(21,1)):
            try:api.rows(base,bad_u,bad_f)
            except ValueError:pass
            else:raise AssertionError('bad wrapper input accepted')
        bad=[set(ns) for ns in base];bad[21].add(21)
        assert json.loads(lib.pair_rows(arr(bad),21,1,100000,1))['status']=='INVALID_INPUT'
out={'status':'PASS_INDEPENDENT_BUILD_AND_FIXTURES','fixtures':len(fixtures),'relabelings_per_fixture':2,
     'domain_checks':checks,'positive':positive,'negative':checks-positive,'retained_full_rows':retained,
     'complete_prefix_equalities':fullchecks,'seconds':time.monotonic()-start,
     'source_sha256':sha(P/'pair_rows.cpp'),'rebuilt_sha256':sha(O/'rebuilt.dylib'),
     'scope':'Generic predicate only under stated valid-prefix and future-option completeness premises. No host integration/search/exclusion.'}
(O/'result.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
