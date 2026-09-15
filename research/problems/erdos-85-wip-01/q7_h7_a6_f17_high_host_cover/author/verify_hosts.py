"""Independent full F17 saved-host structural cover and template checks."""
import pathlib,json,gzip,hashlib,ctypes,array,time,sys
P=pathlib.Path(__file__).parent;S=P/'hosts'
T=pathlib.Path('/Users/rwalters/GitHub/lean-genius/.codex/worktrees/erdos85-sol2-integration/research/problems/erdos-85-wip-01/q7_h7_a6_f18_host/review')
sys.path.insert(0,str(T));import cover
read=lambda p:json.loads(p.read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in read(T/'pins.json').items():assert sha(T/n)==h
for n,h in read(P/'input-pins.json').items():assert sha(P/n)==h
assert not (P/'host-verification.json').exists()
inputs=[json.loads(l) for l in gzip.open(P/'inputs.jsonl.gz','rt')]
assert len(inputs)==77813
pins={str(T/n):sha(T/n) for n in ['cover.py','templates.cpp','templates.dylib']}
for n in ['results.json','survivors.json']+read(S/'results.json')['shards']:pins[str(S/n)]=sha(S/n)
pins[str(P/'inputs.jsonl.gz')]=sha(P/'inputs.jsonl.gz')
(P/'host-verification-launch.json').write_text(json.dumps({'seconds':180,'input_pins':pins,'driver_sha256':sha(pathlib.Path(__file__))},indent=2)+'\n')
start=time.monotonic()
lib=ctypes.CDLL(str(T/'templates.dylib'));U=ctypes.c_uint64;I=ctypes.c_int;lib.verify_prefix_batch.argtypes=[ctypes.POINTER(U),ctypes.POINTER(I),ctypes.POINTER(U),ctypes.POINTER(I),I];lib.verify_prefix_batch.restype=I
summary=read(S/'results.json');seen=[];survivors=[];prunes=structural=leaves=negative=0;max_structural=0
for shard in summary['shards']:
 with gzip.open(S/shard,'rt') as f:
  for l in f:
   r=json.loads(l);inp=inputs[len(seen)];seen.append(r['global_index'])
   for k in ['global_index','completion_index','singleton_index','colouring_index']:assert r[k]==inp[k]
   cert=r['receipt'];assert cert['status']=='COMPLETE' and 0<cert['nodes']<=100000 and cert['empty_vertices']==list(range(42,49))
   cv=cover.check(inp['neighbors'],cert,seconds=max(0,180-(time.monotonic()-start)));assert cv['coverage_proved'];structural+=cv['nodes'];max_structural=max(max_structural,cv['nodes'])
   chosen=[];codes=[]
   for pr in cert['prunes']:
    assert 7<=pr['singleton']<21;chosen.append(pr['chosen']);codes.append(ord('A')+pr['singleton']-7)
   for j,leaf in enumerate(cert['solutions']):chosen.append(leaf);codes.append(ord('.'));survivors.append([r['global_index'],j])
   flat=array.array('Q',(m for row in chosen for m in row));gm=[sum(1<<v for v in ns) for ns in inp['neighbors']]
   assert lib.verify_prefix_batch((U*49)(*gm),(I*7)(*cert['empty_vertices']),(U*len(flat)).from_buffer(flat),(I*len(codes))(*codes),len(codes))==0
   prunes+=len(cert['prunes']);leaves+=len(cert['solutions']);negative+=not cert['solutions']
   assert time.monotonic()-start<180
assert seen==[r['global_index'] for r in inputs] and survivors==read(S/'survivors.json')
assert len(seen)==summary['total']==summary['visited']==77813 and summary['unvisited']==0 and summary['unknown']==[]
assert summary['counts']=={'COMPLETE':77813} and prunes==summary['prunes']==2825313 and leaves==summary['leaves']==1577893
result=dict(status='PASS',source_high_representatives=len(seen),raw_high_assignments=82817,prunes=prunes,survivors=leaves,survivor_domains=14*leaves,negative_highs=negative,structural_nodes=structural,max_structural_nodes=max_structural,seconds=time.monotonic()-start)
for n,h in pins.items():assert sha(pathlib.Path(n))==h
(P/'host-verification.json').write_text(json.dumps(result,indent=2)+'\n');print(result)
