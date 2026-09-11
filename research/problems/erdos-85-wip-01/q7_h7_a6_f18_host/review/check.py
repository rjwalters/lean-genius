import pathlib,json,gzip,hashlib,sqlite3,ctypes,array,time,collections,itertools
import cover
P=pathlib.Path(__file__).parent;S=pathlib.Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3/h7-a6-f18-host-pass');A=pathlib.Path('/tmp/erdos85-sol1-h7-a6-projection-extension');Q=pathlib.Path('/tmp/erdos85-sol1-h7-a6-high-quotient')
def read(p):return json.loads(p.read_text())
for root in [S,A,Q]:
 for f,h in read(root/'pins.json').items():assert hashlib.sha256((root/f).read_bytes()).hexdigest()==h
for f,h in read(S/'input-pins.json').items():assert hashlib.sha256(pathlib.Path(f).read_bytes()).hexdigest()==h
db=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True);db.row_factory=sqlite3.Row
for p in read(S/'premises.json'):
 live=dict(db.execute('select * from review_requests where id=?',(p['id'],)).fetchone());assert live==p and p['status']=='resolved' and p['resolution'].startswith('PASS')
src=read(A/'source-cover-results.json');comp=read(A/'source-completion-results.json');reps=[r for r in read(Q/'representatives.json') if comp['results'][r['completion_index']]['F_index']==18];assert len(reps)==30182 and sum(r['orbit_size'] for r in reps)==38074
high={}
with gzip.open(A/'high-colourings.jsonl.gz','rt') as f:
 for l in f:
  r=json.loads(l);high[r['completion_index'],r['singleton_index']]=r['colourings']
with gzip.open(S/'inputs.jsonl.gz','rt') as f:inputs=[json.loads(l) for l in f]
assert len(inputs)==len(reps)
start=time.monotonic()
for r,q in zip(inputs,reps):
 for k in ['global_index','completion_index','singleton_index','colouring_index']:assert r[k]==q[k]
 ci,j=r['completion_index'],r['singleton_index'];cr=comp['results'][ci];F=src['cases'][18];X=F['representatives'][cr['X_index']];c=high[ci,j][r['colouring_index']]
 edges=set()
 def add(a,b):edges.add(tuple(sorted((a,b))))
 def ren(v):return 42+v if v<7 else v
 for a,b in F['F_edges']+cr['solutions'][j]:add(ren(a),ren(b))
 for d,hs in enumerate(X['singleton_hosts']):
  for e in hs:add(7+d,42+e)
 for d,h in enumerate(c):add(7+d,h)
 for h in range(3):add(18+h,h)
 for p,pair in enumerate(itertools.combinations(range(7),2),21):
  for h in pair:add(p,h)
 actual={(u,v) for u,ns in enumerate(r['neighbors']) for v in ns if u<v};assert actual==edges
 assert all(u in r['neighbors'][v] for u,ns in enumerate(r['neighbors']) for v in ns)
 gm=[sum(1<<v for v in ns) for ns in r['neighbors']]
 assert all((gm[u]&gm[v]).bit_count()<=1 for u in range(49) for v in range(u))
 assert time.monotonic()-start<60
lib=ctypes.CDLL(str(P/'templates.dylib'));U=ctypes.c_uint64;I=ctypes.c_int;lib.verify_prefix_batch.argtypes=[ctypes.POINTER(U),ctypes.POINTER(I),ctypes.POINTER(U),ctypes.POINTER(I),I];lib.verify_prefix_batch.restype=I
summary=read(S/'results.json');seen=[];survivors=[];prunes=structural=leaves=negative=0;max_structural=0
for shard in summary['shards']:
 with gzip.open(S/shard,'rt') as f:
  for l in f:
   r=json.loads(l);inp=inputs[len(seen)];seen.append(r['global_index'])
   for k in ['global_index','completion_index','singleton_index','colouring_index']:assert r[k]==inp[k]
   cert=r['receipt'];assert cert['status']=='COMPLETE' and 0<cert['nodes']<=100000 and cert['empty_vertices']==list(range(42,49))
   cv=cover.check(inp['neighbors'],cert,seconds=max(0,60-(time.monotonic()-start)));assert cv['coverage_proved'];structural+=cv['nodes'];max_structural=max(max_structural,cv['nodes'])
   chosen=[];codes=[]
   for pr in cert['prunes']:
    assert 7<=pr['singleton']<21;chosen.append(pr['chosen']);codes.append(ord('A')+pr['singleton']-7)
   for j,leaf in enumerate(cert['solutions']):chosen.append(leaf);codes.append(ord('.'));survivors.append([r['global_index'],j])
   flat=array.array('Q',(m for row in chosen for m in row));gm=[sum(1<<v for v in ns) for ns in inp['neighbors']]
   assert lib.verify_prefix_batch((U*49)(*gm),(I*7)(*cert['empty_vertices']),(U*len(flat)).from_buffer(flat),(I*len(codes))(*codes),len(codes))==0
   prunes+=len(cert['prunes']);leaves+=len(cert['solutions']);negative+=not cert['solutions']
   assert time.monotonic()-start<60
assert seen==[r['global_index'] for r in reps] and survivors==read(S/'survivors.json')
assert len(seen)==summary['total']==summary['visited']==30182 and summary['unvisited']==0 and summary['unknown']==[]
assert summary['counts']=={'COMPLETE':30182} and prunes==summary['prunes']==601453 and leaves==summary['leaves']==331996
result=dict(status='PASS',source_high_representatives=len(seen),raw_high_assignments=38074,prunes=prunes,survivors=leaves,survivor_domains=14*leaves,negative_highs=negative,structural_nodes=structural,max_structural_nodes=max_structural,seconds=time.monotonic()-start)
(P/'results.json').write_text(json.dumps(result,indent=2)+'\n');(P/'input-pins.json').write_bytes((S/'pins.json').read_bytes());print(result)
