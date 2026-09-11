"""ctypes bridge to the exact complete-row/AC native traversal."""
import ctypes,json,pathlib,math,time
P=pathlib.Path(__file__).parent
lib=ctypes.CDLL(str(P/'filter.dylib'))
lib.native_now.restype=ctypes.c_double
lib.check_rows.argtypes=[ctypes.POINTER(ctypes.c_uint64),ctypes.c_int,ctypes.c_double]
lib.check_rows.restype=ctypes.c_char_p
assert abs(lib.native_now()-time.monotonic())<0.1, 'monotonic clock epochs differ'
def check(adjacency, *, max_nodes=100000, deadline=None):
 if len(adjacency)!=49 or not 0<=max_nodes<2**31:raise ValueError('invalid length/budget')
 masks=[]
 for ns in adjacency:
  ns=set(ns)
  if any(not isinstance(v,int) or v<0 or v>=49 for v in ns):raise ValueError('invalid vertex')
  masks.append(sum(1<<v for v in ns))
 raw=lib.check_rows((ctypes.c_uint64*49)(*masks),max_nodes,math.inf if deadline is None else deadline)
 result=json.loads(raw)
 if result['status']=='INVALID_INPUT':raise ValueError('invalid complete H7 host graph')
 for name in ['initial','remaining']:
  if name in result:result[name]={int(k):v for k,v in result[name].items()}
 return result
