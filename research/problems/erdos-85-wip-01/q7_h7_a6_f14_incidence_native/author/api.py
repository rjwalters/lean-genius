"""Checked ctypes adapter for the necessary singleton-pair projection API."""
import ctypes,hashlib,json,time
from pathlib import Path
P=Path(__file__).parent
class ProjectionAPI:
 def __init__(self):
  pins=json.loads((P/'pins.json').read_text())
  for n in ['projection.cpp','projection.dylib']:
   assert hashlib.sha256((P/n).read_bytes()).hexdigest()==pins[n],n
  self.lib=ctypes.CDLL(str(P/'projection.dylib'));self.U=ctypes.c_uint64
  self.lib.projection_now.restype=ctypes.c_double
  self.lib.check_projection.argtypes=[ctypes.POINTER(self.U),ctypes.c_int,ctypes.c_double];self.lib.check_projection.restype=ctypes.c_char_p
  assert abs(self.lib.projection_now()-time.monotonic())<.1
 def check(self,masks,max_nodes=10000,deadline=None):
  if len(masks)!=49 or any(type(m)!=int or not 0<=m<1<<49 for m in masks):raise ValueError('49 nonnegative 49-bit masks required')
  if type(max_nodes)!=int or not 0<=max_nodes<=10000:raise ValueError('Research choice-node bound is 0..10000')
  if deadline is None:raise ValueError('An explicit monotonic deadline is required')
  out=json.loads(self.lib.check_projection((self.U*49)(*masks),max_nodes,deadline))
  assert out['status'] in ['EMPTY_FAMILY','INFEASIBLE_PROJECTION','FEASIBLE_PROJECTION','UNKNOWN','INVALID']
  return out
