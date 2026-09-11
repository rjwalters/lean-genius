import array,ctypes,json,math,pathlib,time
P=pathlib.Path(__file__).parent;lib=ctypes.CDLL(str(P/'batch.dylib'))
lib.native_now.restype=ctypes.c_double
assert abs(lib.native_now()-time.monotonic())<0.1
lib.batch_hosts.argtypes=[ctypes.POINTER(ctypes.c_uint64),ctypes.POINTER(ctypes.c_int),ctypes.POINTER(ctypes.c_uint64),ctypes.c_int,ctypes.c_int,ctypes.c_double];lib.batch_hosts.restype=ctypes.c_char_p
def check_hosts(base,empty_vertices,host_assignments,*,max_nodes=100000,deadline=None):
 if len(base)!=49 or len(empty_vertices)!=7 or not isinstance(max_nodes,int) or not 0<=max_nodes<2**31:raise ValueError('invalid dimensions/budget')
 if any(not isinstance(e,int) or not 7<=e<49 for e in empty_vertices):raise ValueError('bad empty labels')
 masks=[]
 for ns in base:
  ns=set(ns)
  if any(not isinstance(v,int) or not 0<=v<49 for v in ns):raise ValueError('bad vertex')
  masks.append(sum(1<<v for v in ns))
 flat=array.array('Q')
 for ms in host_assignments:
  if len(ms)!=7 or any(not isinstance(m,int) or not 0<=m<1<<49 for m in ms):raise ValueError('bad host masks')
  flat.extend(ms)
 n=len(flat)//7
 if n>=2**31:raise ValueError('batch too long')
 end=math.inf if deadline is None else float(deadline)
 if math.isnan(end):raise ValueError('invalid deadline')
 result=json.loads(lib.batch_hosts((ctypes.c_uint64*49)(*masks),(ctypes.c_int*7)(*empty_vertices),(ctypes.c_uint64*len(flat)).from_buffer(flat),n,max_nodes,end))
 for r in result:
  if r['status']=='INVALID_INPUT':raise ValueError('invalid base or host assignment')
  for key in ['initial','remaining']:
   if key in r:r[key]={int(k):v for k,v in r[key].items()}
 return result
