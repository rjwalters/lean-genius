"""Independent a7 coverage and singleton/pair-row endpoint verification.

The structural cover checker is accepted 2124. Native row checks independently
enumerate vertex subsets, not the producer's colour-first search.
"""
import ctypes,hashlib,importlib.util,itertools,math,time
from collections import Counter
from pathlib import Path
P=Path(__file__).parent
ROOT=Path('/Users/rwalters/GitHub/lean-genius/.codex/worktrees/erdos85-sol2-integration/research/problems/erdos-85-wip-01')
refpath=ROOT/'q7_h7_a7_f9_host_cover/author/cover_reference.py'
assert hashlib.sha256(refpath.read_bytes()).hexdigest()=='66aa25ed1c6a58f2c1c8ee4672f44dd4b283fe5c17cc4b0b7e97034e16484684'
spec=importlib.util.spec_from_file_location('accepted_cover_reference',refpath)
cv=importlib.util.module_from_spec(spec);spec.loader.exec_module(cv)
U=ctypes.c_uint64
lib=ctypes.CDLL(str(P/'pair_verify.dylib'))
lib.pair_row_exists.argtypes=[ctypes.POINTER(U),ctypes.c_int,ctypes.c_int,ctypes.c_int,ctypes.c_double,ctypes.POINTER(U)]
lib.pair_row_exists.restype=ctypes.c_int
lib.singleton_row_exists.argtypes=[ctypes.POINTER(U),ctypes.c_int,ctypes.c_int,ctypes.c_double,ctypes.POINTER(U)]
lib.singleton_row_exists.restype=ctypes.c_int

def validate_base(base):
    assert len(base)==49
    g=[set(ns) for ns in base];H=set(range(7));S=set(range(7,21));A=set(range(21,42));E=set(range(42,49))
    for u,ns in enumerate(g):
        assert u not in ns and all(type(v) is int and 0<=v<49 and u in g[v] for v in ns)
    sup=[ns&H for ns in g]
    assert all(len(g[h])==8 and not sup[h] for h in H)
    assert all(len(sup[s])==1 for s in S)
    assert all(len(sup[p])==2 and g[p]==sup[p] for p in A)
    assert all(not sup[e] for e in E)
    assert Counter(tuple(sorted(sup[s])) for s in S)==Counter({(h,):2 for h in H})
    assert {tuple(sorted(sup[p])) for p in A}==set(itertools.combinations(range(7),2))
    assert all(len(g[u]&g[v])<=1 for u in range(49) for v in range(u))
    for e in E:
        d=len(g[e]&E);assert d<=3 and len(g[e]&S)==7-2*d
    for s in S:
        d=len(g[s]&E);assert d in (1,2) and len(g[s]&S)==5-2*d
        assert all(sup[t]!=sup[s] for t in g[s]&S)
    for h in H:assert sorted(len(g[s]&E) for s in S if h in sup[s])==[1,2]
    return g

def check(base,receipt,*,fixed=None,max_nodes=100000,seconds=60,verify_partial=False):
    assert type(max_nodes) is int and 0<=max_nodes<2**31
    assert math.isfinite(seconds) and 0<=seconds<=86400
    start=time.monotonic();deadline=start+seconds
    g=validate_base(base)
    covered=cv.check(g,receipt,fixed=fixed,max_nodes=max_nodes,seconds=max(0,deadline-time.monotonic()))
    if not covered['coverage_proved'] and (not verify_partial or len(receipt['order'])<7):
        return dict(covered,endpoint_status='NOT_CHECKED_UNKNOWN')
    E=receipt['empty_vertices'];order=receipt['order'];assert E==list(range(42,49))
    opts=cv.options(g,E)
    if fixed is not None:opts=[[m] for m in fixed]
    future=[0]*8
    for d in range(6,-1,-1):
        future[d]=future[d+1]
        for m in opts[order[d]]:future[d]|=m
    checks=Counter();nodes=0
    def graph(chosen):
        out=[set(ns) for ns in g]
        for i,mask in enumerate(chosen):
            for p in range(21,42):
                if mask>>p&1:out[E[i]].add(p);out[p].add(E[i])
        return (U*49)(*[sum(1<<v for v in ns) for ns in out])
    def endpoint(a,u,pair,possible,expect):
        nonlocal nodes
        remaining=deadline-time.monotonic()
        if remaining<=0:raise TimeoutError('Endpoint verifier time cap')
        n=U()
        if pair:status=lib.pair_row_exists(a,u,int(possible),max_nodes,remaining,ctypes.byref(n))
        else:status=lib.singleton_row_exists(a,u,max_nodes,remaining,ctypes.byref(n))
        nodes+=n.value
        if status==2:raise TimeoutError('Endpoint verifier node/time cap')
        assert status==expect,(u,pair,status,expect)
    for r in receipt['prunes']:
        a=graph(r['chosen']);is_pair='pair_vertex' in r
        assert is_pair != ('singleton' in r)
        if is_pair:
            u=r['pair_vertex'];assert type(u) is int and 21<=u<42
            assert r['future_pairs']==future[r['depth']]
            endpoint(a,u,True,bool(future[r['depth']]>>u&1),0);checks['pair_prunes']+=1
        else:
            u=r['singleton'];assert type(u) is int and 7<=u<21
            endpoint(a,u,False,False,0);checks['singleton_prunes']+=1
    for chosen in receipt['solutions']:
        a=graph(chosen)
        for u in range(7,42):endpoint(a,u,u>=21,False,1)
        checks['positive_leaves']+=1
    return dict(covered,endpoint_status='PASS',endpoint_counts=dict(checks),endpoint_nodes=nodes,
                seconds=time.monotonic()-start)
