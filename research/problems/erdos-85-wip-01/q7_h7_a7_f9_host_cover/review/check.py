from pathlib import Path
import json,gzip,hashlib,itertools,ctypes,importlib.util,time,sqlite3
O=Path(__file__).parent;P=Path('/Users/rwalters/lean-genius-q7-outside-first-20260910/h7-a7-f9-host-pass');S=P.parent/'h7-a7-noncycle-singleton-projection';H=P.parent/'h7-a7-f9-projection-extension';N=O.parent/'h7-host-prefix-native-verifier';C=O.parent/'h7-host-receipt-cover-verifier';assert not (O/'results.json').exists()
inputs=[P/f for f in ['results.json','survivors.json','receipts-000.jsonl.gz','premises.json','api-pins.json','launch.json','run.py','inputs.py']]+[S/'results.json',S/'completion-results.json',H/'high-results.json',N/'verify.cpp',N/'verify.dylib',C/'cover.py']
pins={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in inputs};(O/'input-pins.json').write_text(json.dumps(pins,indent=2)+'\n')
c=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True);c.row_factory=sqlite3.Row
for old in json.loads((P/'premises.json').read_text()):
 live=dict(c.execute('select * from review_requests where id=?',(old['id'],)).fetchone());assert live==old and live['status']=='resolved' and live['resolution'].startswith('PASS')
for f,h in json.loads((P/'api-pins.json').read_text()).items():assert hashlib.sha256((Path('/tmp/erdos85-sol1-h7-monotone-pair-host-api')/f).read_bytes()).hexdigest()==h
sp=importlib.util.spec_from_file_location('structural',C/'cover.py');cv=importlib.util.module_from_spec(sp);sp.loader.exec_module(cv)
lib=ctypes.CDLL(str(N/'verify.dylib'));lib.star_count.argtypes=[ctypes.POINTER(ctypes.c_uint64),ctypes.c_int,ctypes.POINTER(ctypes.c_uint64)];lib.star_count.restype=ctypes.c_int;lib.verify_prefixes.argtypes=[ctypes.POINTER(ctypes.c_uint64),ctypes.POINTER(ctypes.c_int),ctypes.POINTER(ctypes.c_int),ctypes.POINTER(ctypes.c_uint64),ctypes.c_int,ctypes.POINTER(ctypes.c_uint64)];lib.verify_prefixes.restype=ctypes.c_int
cover=json.loads((S/'results.json').read_text());done=json.loads((S/'completion-results.json').read_text());highs=json.loads((H/'high-results.json').read_text());summary=json.loads((P/'results.json').read_text());sgraph={(r['source_index'],j):es for r in done['results'] if r['F_index']==9 and r['status']=='COMPLETE' for j,es in enumerate(r['solutions'])};expected=[(ci,pi) for ci,r in enumerate(highs['results']) for pi in range(len(r['pairings']))]
assert len(expected)==28336
start=time.monotonic();seen=[];survivors=[];prefixes=structural=domains=rows=negative=0;native_nodes=ctypes.c_uint64();E=list(range(42,49));Ea=(ctypes.c_int*7)(*E);K=list(itertools.combinations(range(7),2));maxstructural=0
for shard in summary['receipt_shards']:
 with gzip.open(P/shard,'rt') as stream:
  for line in stream:
   if time.monotonic()-start>60:raise TimeoutError('independent full receipt audit reached60s')
   record=json.loads(line);ci,pi=record['case_index'],record['pairing_index'];seen.append((ci,pi));assert (ci,pi)==expected[len(seen)-1];hr=highs['results'][ci];key=(hr['source_index'],hr['singleton_index']);assert key==(record['source_index'],record['singleton_index']);rep=cover['representatives'][key[0]];assert rep['F_index']==9
   g=[set() for _ in range(49)]
   def add(u,v):g[u].add(v);g[v].add(u)
   ren=lambda u:u+42 if u<7 else u
   for u,v in rep['F_edges']+sgraph[key]:add(ren(u),ren(v))
   for s,hs in enumerate(rep['singleton_hosts'],7):
    for e in hs:add(s,e+42)
   for p,(a,b) in enumerate(K,21):add(p,a);add(p,b)
   for h,d in enumerate(hr['pairings'][pi]):add(h,14+h);add(h,7+d)
   r=record['receipt'];assert r['status']=='COMPLETE' and r['nodes']<=100000 and r['empty_vertices']==E
   cvout=cv.check(g,r);assert cvout['coverage_proved'];structural+=cvout['nodes'];maxstructural=max(maxstructural,cvout['nodes'])
   masks=[sum(1<<v for v in ns) for ns in g];ga=(ctypes.c_uint64*49)(*masks);order=(ctypes.c_int*7)(*r['order']);flat=[v for p in r['prunes'] for v in [p['depth'],p['singleton'],*p['chosen']]];ra=(ctypes.c_uint64*len(flat))(*flat)
   assert lib.verify_prefixes(ga,Ea,order,ra,len(r['prunes']),ctypes.byref(native_nodes))==0,(ci,pi)
   prefixes+=len(r['prunes']);negative+=not r['solutions']
   for si,chosen in enumerate(r['solutions']):
    full=masks[:]
    for e,m in zip(E,chosen):
     full[e]|=m
     while m:
      bit=m&-m;m-=bit;full[bit.bit_length()-1]|=1<<e
    a=(ctypes.c_uint64*49)(*full)
    for s in range(7,21):
     n=lib.star_count(a,s,ctypes.byref(native_nodes));assert n>0;domains+=1;rows+=n
    survivors.append([ci,pi,si])
assert seen==expected and prefixes==3545834 and len(survivors)==99224 and negative==6194
assert survivors==json.loads((P/'survivors.json').read_text()) and summary['counts']=={'COMPLETE':28336} and summary['unvisited']==0 and not summary['unknown_high_graphs']
for f,h in pins.items():assert hashlib.sha256(Path(f).read_bytes()).hexdigest()==h
out=dict(status='PASS',given_high_graphs=len(seen),prefixes=prefixes,survivors=len(survivors),negative_high_graphs=negative,structural_nodes=structural,max_structural_nodes=maxstructural,survivor_domains=domains,survivor_rows=rows,native_subset_nodes=native_nodes.value,seconds=time.monotonic()-start,scope='Independent full local-product receipt cover, direct-star empty prefix checks and positive survivor domain checks. Exact ordered2121 inputs and survivor export; no host/residual family search.')
(O/'results.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
