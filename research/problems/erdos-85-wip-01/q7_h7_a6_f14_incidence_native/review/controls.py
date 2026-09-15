import ctypes,json,time,hashlib
from pathlib import Path
D=Path(__file__).parent;P=Path('/Users/rwalters/lean-genius-h7-a6-f14-incidence-native-sol2-20260915')
lib=ctypes.CDLL(str(P/'projection.dylib'));U=ctypes.c_uint64
lib.check_projection.argtypes=[ctypes.POINTER(U),ctypes.c_int,ctypes.c_double];lib.check_projection.restype=ctypes.c_char_p
fixtures=json.loads((P/'fixtures.json').read_text());base=fixtures[0]['graph'];checks=[]
def call(g,cap=10000,seconds=5):return json.loads(lib.check_projection(None if g is None else (U*49)(*g),cap,time.monotonic()+seconds))
for label,g,cap,seconds,status in [('null',None,1,5,'INVALID'),('negative_cap',base,-1,5,'INVALID'),('oversize_cap',base,1000001,5,'INVALID'),('expired',base,10000,-1,'UNKNOWN'),('zero_cap',base,0,5,'UNKNOWN'),('nan_deadline',base,10,float('nan'),'INVALID'),('infinite_deadline',base,10,float('inf'),'INVALID')]:
 out=call(g,cap,seconds);assert out['status']==status;checks.append(label)
for label,u,bit in [('loop',0,0),('out_of_range',0,49),('asymmetry',0,next(v for v in range(49) if base[0]>>v&1))]:
 g=base.copy();g[u]^=1<<bit;assert call(g)['status']=='INVALID';checks.append(label)
r=call(base);n=r['nodes'];assert r['status']=='INFEASIBLE_PROJECTION' and n>0
assert call(base,n)['status']=='INFEASIBLE_PROJECTION' and call(base,n-1)['status']=='UNKNOWN';checks.append('exact_node_boundary')
x=json.loads((P/'unit-results.json').read_text())['positive'];chosen={int(u):{s for s in range(14) if mask>>s&1} for u,mask in x['witness'].items()}
assert set(chosen)==set(range(21,42))
assert all(sum(s in f for f in chosen.values())==x['capacity'][s] for s in range(14))
assert all(len(chosen[u]&chosen[v])<=1 for u in chosen for v in chosen if u<v)
assert all(x['witness'][u] in masks for u,masks in x['families'].items())
checks.append('synthetic_positive_serialization')
out={'status':'PASS_INDEPENDENT_CONTROLS','checks':checks,'dylib_sha256':hashlib.sha256((P/'projection.dylib').read_bytes()).hexdigest(),'scope':'API malformed/limit controls and synthetic positive output only; no positive H7 graph claim.'}
(D/'CONTROLS_REVIEW.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
