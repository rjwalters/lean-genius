import ctypes
import json
from pathlib import Path

P=Path(__file__).parent
lib=ctypes.CDLL(str(P/'pair_rows.dylib'))
U=ctypes.c_uint64
lib.pair_rows.argtypes=[ctypes.POINTER(U),ctypes.c_int,ctypes.c_int,ctypes.c_int,ctypes.c_double]
lib.pair_rows.restype=ctypes.c_char_p

def rows(adjacency,vertex,future_host_possible,*,max_nodes=100000,seconds=1):
    if len(adjacency)!=49 or not isinstance(max_nodes,int) or not 0<=max_nodes<2**31:
        raise ValueError('invalid graph length or node bound')
    if not isinstance(vertex,int) or not 21<=vertex<42:
        raise ValueError('invalid vertex argument')
    if type(future_host_possible) is not bool:
        raise ValueError('future-host flag must be a bool')
    masks=[]
    for ns in adjacency:
        ns=set(ns)
        if any(not isinstance(v,int) or not 0<=v<49 for v in ns): raise ValueError('invalid vertex')
        masks.append(sum(1<<v for v in ns))
    return json.loads(lib.pair_rows((U*49)(*masks),vertex,int(future_host_possible),max_nodes,seconds))
