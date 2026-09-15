"""Enumerate empty hosts for a fixed a6/a7 high assignment."""
import ctypes,json,math,pathlib
P=pathlib.Path(__file__).parent;lib=ctypes.CDLL(str(P/'hosts.dylib'))
lib.enumerate_hosts.argtypes=[ctypes.POINTER(ctypes.c_uint64),ctypes.c_int,ctypes.c_double];lib.enumerate_hosts.restype=ctypes.c_char_p
def enumerate_hosts(adjacency,*,max_nodes=100000,seconds=60):
 if len(adjacency)!=49 or not isinstance(max_nodes,int) or not 0<=max_nodes<2**31:raise ValueError('invalid length/budget')
 if not math.isfinite(seconds) or abs(seconds)>86400:raise ValueError('invalid duration')
 masks=[]
 for ns in adjacency:
  ns=set(ns)
  if any(not isinstance(v,int) or not 0<=v<49 for v in ns):raise ValueError('invalid vertex')
  masks.append(sum(1<<v for v in ns))
 result=json.loads(lib.enumerate_hosts((ctypes.c_uint64*49)(*masks),max_nodes,seconds))
 if result['status']=='INVALID_INPUT':raise ValueError('invalid high/empty/singleton base')
 return result
