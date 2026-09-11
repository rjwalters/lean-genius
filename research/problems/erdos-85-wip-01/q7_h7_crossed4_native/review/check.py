import pathlib,json,gzip,hashlib,time,itertools,ctypes
P=pathlib.Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3/h7-crossed4-native');O=pathlib.Path(__file__).parent
pins=json.loads((P/'pins.json').read_text());assert all(hashlib.sha256((P/f).read_bytes()).hexdigest()==h for f,h in pins.items())
data=json.loads(gzip.decompress((P/'results.json.gz').read_bytes()));assert [r['assignment_index'] for r in data['results']]==list(range(3780));assert sum(r['status']=='INFEASIBLE_LOCAL' for r in data['results'])==401;assert sum(r['status']=='INFEASIBLE_ARC' for r in data['results'])==3379
lib=ctypes.CDLL(str(O/'subsets.dylib'));U=ctypes.c_uint64;I=ctypes.c_int64
lib.verify_domain.argtypes=[ctypes.POINTER(U),ctypes.c_int,ctypes.POINTER(U),ctypes.c_int,I,ctypes.c_double,ctypes.POINTER(I),ctypes.POINTER(I)];lib.verify_domain.restype=ctypes.c_int
start=time.monotonic();summaries=[];allrows=events=failures=0

def bits(n):
 while n:
  b=n&-n;yield b.bit_length()-1;n-=b
for result in data['results']:
 idx=result['assignment_index'];g=[sum(1<<v for v in ns) for ns in result['adjacency']];outside=[v for v in range(7,49) if not g[0]>>v&1];assert len(outside)==34;nodes=0
 def tick():
  global nodes
  nodes+=1
  if nodes>100000 or time.monotonic()-start>60:raise TimeoutError
 try:
  domains={}
  vertices=outside if result['status']=='INFEASIBLE_ARC' else [result['local_result']['vertex']]
  for u in vertices:
   expected=result['initial'][str(u)] if result['status']=='INFEASIBLE_ARC' else []
   used=I();found=I();remaining=60-(time.monotonic()-start)
   if remaining<=0:raise TimeoutError
   status=lib.verify_domain((U*49)(*g),u,(U*len(expected))(*expected),len(expected),100000-nodes,remaining,ctypes.byref(used),ctypes.byref(found));nodes+=used.value
   if status==-1:raise TimeoutError
   assert status==1,(idx,u,status,found.value,len(expected))
   answers=set(expected)
   if result['status']=='INFEASIBLE_LOCAL':
    assert not answers,(idx,u,'local negative has legal row')
    continue
   assert len(result['initial'][str(u)])==len(set(result['initial'][str(u)]))
   assert answers==set(result['initial'][str(u)]),(idx,u,len(answers),len(result['initial'][str(u)]))
   domains[u]=answers;allrows+=len(answers)
  for event in result.get('events',[]):
   u,v=event['vertex'],event['against'];assert u!=v
   removed=set(event['removed']);assert len(removed)==len(event['removed']) and removed<=domains[u]
   for a in removed:
    for b in domains[v]:
     # Compare full final neighbour sets, not the author's old/new split.
     assert ((a>>v)&1)!=((b>>u)&1) or ((g[u]|a)&(g[v]|b)).bit_count()>1
     failures+=1
   domains[u]-=removed;events+=1
  if result['status']=='INFEASIBLE_ARC':assert not domains[result['empty_vertex']]
  summaries.append({'source_index':idx,'status':'VERIFIED','generation_nodes':nodes})
 except TimeoutError:
  summaries.append({'source_index':idx,'status':'UNKNOWN','generation_nodes':nodes});break
assert all(hashlib.sha256((P/f).read_bytes()).hexdigest()==h for f,h in pins.items())
out={'results':summaries,'verified':sum(r['status']=='VERIFIED' for r in summaries),'unvisited':3780-len(summaries),'rows':allrows,'events':events,'failed_supports':failures,'nodes':sum(r['generation_nodes'] for r in summaries),'seconds':time.monotonic()-start,'pins':pins,'method':'Independent C++ increasing-candidate-subset complete row enumeration, exact row-set comparison; sequential deletion replay using full final neighbour intersections. No author generator/filter imports.'}
(O/'results.json').write_text(json.dumps(out,indent=2)+'\n');print({k:v for k,v in out.items() if k not in ['results','pins']})
