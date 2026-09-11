"""Combinatorial unit fixtures, not candidate graph searches."""
import ctypes,itertools,json,pathlib
P=pathlib.Path(__file__).parent;lib=ctypes.CDLL(str(P/'high.dylib'));lib.high_pairings.argtypes=[ctypes.POINTER(ctypes.c_uint64),ctypes.c_int,ctypes.c_double];lib.high_pairings.restype=ctypes.c_char_p
def call(g,cap=100000,seconds=60):return json.loads(lib.high_pairings((ctypes.c_uint64*21)(*g),cap,seconds))
def pairings(vs):
 if not vs:yield [];return
 a=vs[0]
 for j,b in enumerate(vs[1:],1):
  for tail in pairings(vs[1:j]+vs[j+1:]):yield [(a,b)]+tail
results=[]
for mode in range(4):
 g=[0]*21
 for d,e in enumerate([0,1,2,3,4,3,4,5,6,5,6]):g[7+d]=1<<e
 for h in range(3):g[18+h]=127^(1<<h)
 if mode==1:g[18]|=1<<7 # forbid unique first mixed pair by adjacency
 if mode==2:g[7+3]|=1<<8;g[7+4]|=1<<8 # a new common S neighbour removes some double pairings
 if mode==3:g[7+3]|=1<<(7+4);g[7+4]|=1<<(7+3) # adjacent double pairs remain allowed unless they share another neighbour
 expected=[]
 for ds in itertools.permutations(range(11),3):
  if any(g[18+h]&(1<<(7+d)) or g[18+h]&g[7+d] for h,d in enumerate(ds)):continue
  for pairs in pairings([d for d in range(11) if d not in ds]):
   if any(g[7+a]&g[7+b] for a,b in pairs):continue
   c=[-1]*11
   for h,d in enumerate(ds):c[d]=h
   for h,(a,b) in enumerate(pairs,3):c[a]=c[b]=h
   expected.append(c)
 answer=call(g);assert answer['status']=='COMPLETE' and answer['colourings']==expected
 assert call(g,0)['status']=='UNKNOWN' and call(g,seconds=-1)['status']=='UNKNOWN'
 results.append(dict(mode=mode,count=len(expected),nodes=answer['nodes']))
assert results[0]['count']>0 and results[1]['count']==0
out=dict(status='PASS',fixtures=4,results=results);(P/'high-test-results.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
