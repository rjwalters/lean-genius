"""Check saved host-cover certificates without resuming the producer."""
import array
import collections
import ctypes
import gzip
import hashlib
import importlib.util
import json
import time
from highs import ROOT, OUT, inputs, graph
import itertools

def given_high(g, pairing):
    a = [set() for _ in range(49)]
    ren = lambda v: v+42 if v < 7 else v
    def add(u,v): a[u].add(v);a[v].add(u)
    for u in range(21):
        for v in g[u]:
            if u<v: add(ren(u),ren(v))
    for v,(i,j) in enumerate(itertools.combinations(range(7),2),21): add(v,i);add(v,j)
    for h,d in enumerate(pairing): add(h,14+h);add(h,7+d)
    return a


REF = ROOT/'q7_h7_a7_f9_host_cover/author'
spec=importlib.util.spec_from_file_location('cover_reference',REF/'cover_reference.py')
cv=importlib.util.module_from_spec(spec)
spec.loader.exec_module(cv)
lib=ctypes.CDLL(str(REF/'verify.dylib'))
U,I=ctypes.c_uint64,ctypes.c_int
lib.verify_prefix_batch.argtypes=[ctypes.POINTER(U),ctypes.POINTER(I),ctypes.POINTER(U),ctypes.POINTER(I),I]
lib.verify_prefix_batch.restype=I

cover,cases=inputs()
high=json.loads((OUT/'high-results.json').read_text())
result=json.loads((OUT/'hosts/results.json').read_text())
expected=[(r['case_index'],pi) for r in high['results'] for pi in range(len(r['pairings']))]
start=time.monotonic()
deadline=start+120
seen=[]
counts=collections.Counter()
prunes=leaves=negative=structural=0
unknown_prunes=unknown_leaves=0
for name in result['receipt_shards']:
    with gzip.open(OUT/'hosts'/name,'rt') as stream:
        for line in stream:
            if time.monotonic()>=deadline:
                raise TimeoutError('Independent receipt verification capped; producer remains frozen')
            record=json.loads(line)
            ci,pi=record['case_index'],record['pairing_index']
            assert (ci,pi)==expected[len(seen)]
            seen.append((ci,pi))
            h=high['results'][ci]
            assert (record['source_index'],record['singleton_index'])==(h['source_index'],h['singleton_index'])
            cert=record['receipt']
            counts[cert['status']]+=1
            if cert['status']=='UNKNOWN':
                unknown_prunes+=len(cert['prunes'])
                unknown_leaves+=len(cert['solutions'])
                continue
            assert cert['status']=='COMPLETE'
            base=given_high(graph(cover,cases[ci]),h['pairings'][pi])
            checked=cv.check(base,cert,max_nodes=100000,seconds=max(0,deadline-time.monotonic()))
            assert checked['coverage_proved']
            structural+=checked['nodes']
            E=cert['empty_vertices']
            assert E==list(range(42,49))
            chosen=[]
            codes=[]
            for prune in cert['prunes']:
                s=prune['singleton']
                assert 7<=s<=20
                chosen.append(prune['chosen'])
                codes.append(ord('A')+s-7)
            for j,leaf in enumerate(cert['solutions']):
                chosen.append(leaf)
                codes.append(ord('.'))
            flat=array.array('Q',(m for row in chosen for m in row))
            assert flat.itemsize==8
            status=lib.verify_prefix_batch((U*49)(*[sum(1<<v for v in ns) for ns in base]),
                (I*7)(*E),(U*len(flat)).from_buffer(flat),(I*len(codes))(*codes),len(codes))
            assert status==0,(ci,pi,status)
            prunes+=len(cert['prunes'])
            leaves+=len(cert['solutions'])
            negative+=not cert['solutions']
assert len(seen)==result['visited'] and len(expected)-len(seen)==result['unvisited']
assert dict(counts)==result['counts']
assert (prunes,leaves,negative)==(result['pruned_prefixes']-unknown_prunes,result['surviving_host_leaves_complete'],result['negative_high_graphs'])
assert unknown_leaves==result['host_leaves_unknown_cases']
summary=dict(status='PASS_COMPLETED_RECEIPTS',visited=len(seen),counts=dict(counts),
    unvisited=result['unvisited'],prunes=prunes,leaves=leaves,negative=negative,
    structural_nodes=structural,seconds=time.monotonic()-start,
    verifier_pins={f:hashlib.sha256((REF/f).read_bytes()).hexdigest() for f in ['cover_reference.py','verify.dylib']},
    scope='Saved COMPLETE receipt coverage and direct singleton-star endpoints. UNKNOWN/unvisited unchanged. No residual graph exclusion.')
(OUT/'host-verification.json').write_text(json.dumps(summary,indent=2)+'\n')

print(json.dumps(summary))
