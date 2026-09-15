import ctypes,json,time
from pathlib import Path
P=Path(__file__).parent;U=ctypes.c_uint64;lib=ctypes.CDLL(str(P/'projection.dylib'));lib.check_projection.argtypes=[ctypes.POINTER(U),ctypes.c_int,ctypes.c_double];lib.check_projection.restype=ctypes.c_char_p
g=json.loads((P/'fixtures.json').read_text())[0]['graph'];checks=[]
for label,u,v in [('asymmetric',0,7),('self_loop',7,7),('outside_vertex',0,60)]:
 h=g[:];h[u]^=1<<v
 r=json.loads(lib.check_projection((U*49)(*h),10000,time.monotonic()+5));assert r['status']=='INVALID';checks.append(label)
r=json.loads(lib.check_projection((U*49)(*g),10000,float('inf')));assert r['status']=='INVALID';checks.append('infinite_deadline')
full=json.loads(lib.check_projection((U*49)(*g),10000,time.monotonic()+5));assert full['status']=='INFEASIBLE_PROJECTION' and full['nodes']>1
r=json.loads(lib.check_projection((U*49)(*g),full['nodes']-1,time.monotonic()+5));assert r['status']=='UNKNOWN' and r['nodes']==full['nodes']-1;checks.append('exact_node_boundary')
(P/'controls-results.json').write_text(json.dumps({'status':'PASS_EXTRA_CONTROLS','checks':checks},indent=2)+'\n');print(checks)
