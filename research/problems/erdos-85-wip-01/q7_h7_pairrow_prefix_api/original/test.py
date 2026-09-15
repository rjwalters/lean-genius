"""Bounded fixture checks only; never runs the host producer."""
import ctypes
import gzip
import hashlib
import importlib.util
import itertools
import json
import time
from pathlib import Path
import api
import reference

P=Path(__file__).parent
SOURCE=Path('/Users/rwalters/lean-genius-h7-f5-sol2-20260915')
ROOT=Path('/Users/rwalters/GitHub/lean-genius/.codex/worktrees/erdos85-sol2-integration/research/problems/erdos-85-wip-01')
for name,h in json.loads((SOURCE/'host-pins.json').read_text()).items(): assert hashlib.sha256((SOURCE/name).read_bytes()).hexdigest()==h
launch=json.loads((SOURCE/'high-launch.json').read_text())
basepath=Path(launch['source_path'])
cover=json.loads((basepath/'results.json').read_text())
done=json.loads((basepath/'completion-results.json').read_text())
edges={(r['source_index'],j):es for r in done['results'] if r['F_index']==5 for j,es in enumerate(r['solutions'])}
high=json.loads((SOURCE/'high-results.json').read_text())['results']
host=json.loads((SOURCE/'hosts/results.json').read_text())
fixtures=[];index=0
for shard in host['receipt_shards']:
    for line in gzip.open(SOURCE/'hosts'/shard,'rt'):
        r=json.loads(line)
        if index%431==0 and r['receipt']['solutions']: fixtures.append(r)
        index+=1
assert len(fixtures)==17
spec=importlib.util.spec_from_file_location('host_reference',ROOT/'q7_h7_a7_f9_host_cover/author/cover_reference.py')
cv=importlib.util.module_from_spec(spec);spec.loader.exec_module(cv)
oldpath=ROOT/'q7_h7_a7_f9_closure/review/row-verifier/rows.dylib'
old=ctypes.CDLL(str(oldpath));U=ctypes.c_uint64
old.enumerate_rows.argtypes=[ctypes.POINTER(U),ctypes.c_int,ctypes.POINTER(U),ctypes.POINTER(U)]
old.enumerate_rows.restype=ctypes.c_int
buf=(U*1024)();oldnodes=U()
start=time.monotonic();deadline=start+120
checks=positive=retained=full_equal=0
for fixture in fixtures:
    h=high[fixture['case_index']];rep=cover['representatives'][h['source_index']]
    base=[set() for _ in range(49)]
    def add(g,u,v): g[u].add(v);g[v].add(u)
    def ren(u): return u+42 if u<7 else u
    for u,v in rep['F_edges']+edges[h['source_index'],h['singleton_index']]: add(base,ren(u),ren(v))
    for s,hs in enumerate(rep['singleton_hosts'],7):
        for e in hs: add(base,s,42+e)
    for p,(u,v) in enumerate(itertools.combinations(range(7),2),21): add(base,p,u);add(base,p,v)
    for u,d in enumerate(h['pairings'][fixture['pairing_index']]): add(base,u,14+u);add(base,u,7+d)
    cert=fixture['receipt'];chosen=cert['solutions'][0];order=cert['order']
    opts=cv.options(base,list(range(42,49)))
    def partial(depth):
        g=[set(ns) for ns in base]
        for i in order[:depth]:
            for p in range(21,42):
                if chosen[i]>>p&1:add(g,42+i,p)
        return g
    full=partial(7);fullrows={}
    for p in range(21,42):
        n=old.enumerate_rows((U*49)(*[sum(1<<v for v in ns) for ns in full]),p,buf,ctypes.byref(oldnodes))
        assert n>=0
        fullrows[p]=set(buf[:n])
    for depth in (0,3,7):
        g=partial(depth)
        for p in range(21,42):
            assert time.monotonic()<deadline,'Fixture cap, no search result inferred'
            future=reference.future_possible(opts,order,depth,p)
            native=api.rows(g,p,future)
            assert native['status']=='COMPLETE'
            expected=reference.rows(g,p,future)
            assert len(native['rows'])==len(set(native['rows'])) and set(native['rows'])==expected
            assert fullrows[p]<=expected
            checks+=1;positive+=bool(expected);retained+=len(fullrows[p])
            if depth==7: assert expected==fullrows[p];full_equal+=1
    assert api.rows(base,21,True,max_nodes=0)['status']=='UNKNOWN'
    assert json.loads(api.lib.pair_rows((U*49)(*[sum(1<<v for v in ns) for ns in base]),7,1,100000,1))['status']=='INVALID_INPUT'
    for bad_vertex,bad_future in ((7,True),(2**32+21,True),(21,0.5)):
        try: api.rows(base,bad_vertex,bad_future)
        except ValueError: pass
        else: raise AssertionError('invalid argument accepted')
assert positive>0 and retained>0
result={'status':'PASS_FIXTURES','fixtures':len(fixtures),'domain_checks':checks,'positive_domains':positive,
        'retained_complete_rows':retained,'complete_prefix_equalities':full_equal,'seconds':time.monotonic()-start,
        'accepted_row_library_sha256':hashlib.sha256(oldpath.read_bytes()).hexdigest(),
        'scope':'Fixture/domain checks only; valid-a7-prefix and future-option coverage remain theorem premises. No host search or graph exclusion.'}
(P/'test-results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
