"""Independent structural cover + singleton/pair endpoint checker."""
import ctypes
import importlib.util
from pathlib import Path
ROOT=Path('/Users/rwalters/GitHub/lean-genius/.codex/worktrees/erdos85-sol2-integration/research/problems/erdos-85-wip-01')
def module(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
cv=module('cover_ref',ROOT/'q7_h7_a7_f9_host_cover/author/cover_reference.py')
pair=module('pair_ref',Path('/Users/rwalters/lean-genius-h7-pairrow-prefix-sol2-20260915/reference.py'))
lib=ctypes.CDLL(str(ROOT/'q7_h7_a7_f9_host_cover/author/verify.dylib'))
U,I=ctypes.c_uint64,ctypes.c_int
lib.verify_prefix_batch.argtypes=[ctypes.POINTER(U),ctypes.POINTER(I),ctypes.POINTER(U),ctypes.POINTER(I),I]
lib.verify_prefix_batch.restype=I

def check(base,receipt,*,seconds=60,fixed=None):
    coverage=cv.check(base,receipt,fixed=fixed,max_nodes=100000,seconds=seconds)
    options=cv.options(base,list(range(42,49)))
    if fixed is not None:
        assert len(fixed)==7 and all(m in opts for m,opts in zip(fixed,options))
        options=[[m] for m in fixed]
    singles=[];codes=[];pair_prunes=0
    for r in receipt['prunes']:
        if 'singleton' in r:
            assert 'pair_vertex' not in r
            singles.append(r['chosen']);codes.append(ord('A')+r['singleton']-7)
            assert 7<=r['singleton']<21
        else:
            p=r['pair_vertex'];assert 21<=p<42
            future=0
            for i in receipt['order'][r['depth']:]:
                for option in options[i]:future|=option
            assert r['future_pairs']==future
            g=[set(ns) for ns in base]
            for i,mask in enumerate(r['chosen']):
                for v in range(21,42):
                    if mask>>v&1:g[v].add(42+i);g[42+i].add(v)
            assert not pair.rows(g,p,bool(future>>p&1))
            pair_prunes+=1
    for leaf in receipt['solutions']: singles.append(leaf);codes.append(ord('.'))
    if singles:
        flat=[m for chosen in singles for m in chosen]
        assert lib.verify_prefix_batch((U*49)(*[sum(1<<v for v in ns) for ns in base]),
            (I*7)(*range(42,49)),(U*len(flat))(*flat),(I*len(codes))(*codes),len(codes))==0
    return {'coverage_proved':coverage['coverage_proved'],'pair_prunes':pair_prunes,
            'singleton_prunes':len(receipt['prunes'])-pair_prunes,'leaves':len(receipt['solutions'])}
