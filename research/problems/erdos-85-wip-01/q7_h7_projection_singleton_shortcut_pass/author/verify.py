import pathlib,json,gzip,ctypes,array,time,importlib.util,collections
P=pathlib.Path(__file__).parent;A=pathlib.Path('/tmp/erdos85-sol1-h7-projection-extension');lib=ctypes.CDLL(str(P/'verify.dylib'));u64=ctypes.c_uint64;u32=ctypes.c_uint32;u8=ctypes.c_uint8
lib.verify_graph.argtypes=[ctypes.POINTER(u64),ctypes.c_int];lib.verify_graph.restype=ctypes.c_int
lib.verify_batch.argtypes=[ctypes.POINTER(u64),ctypes.POINTER(u32),ctypes.POINTER(u8),ctypes.c_int,ctypes.c_double,ctypes.POINTER(ctypes.c_int)];lib.verify_batch.restype=ctypes.c_int
# Fixed-fixture independent C++ direct-star cross-check before family verification.
B=P.parent/'h7-singleton-host-row-shortcut';sp=importlib.util.spec_from_file_location('compact',B/'compact.py');api=importlib.util.module_from_spec(sp);sp.loader.exec_module(api)
fixtures=json.loads((P.parent/'h7-singleton-complete-row-api/fixtures.json').read_text());tests=0
for adj in fixtures:
 rows=api.evaluate(api.prepare(adj),{p:sum(1<<e for e in adj[p] if e>=42) for p in range(21,42)});g=(u64*49)(*[sum(1<<v for v in ns) for ns in adj]);bad=next((s for s,r in rows.items() if not r),None);code=ord('.') if bad is None else ord('A')+bad-7
 assert lib.verify_graph(g,code)==1;tests+=1
 for s,rs in rows.items():assert bool(lib.verify_graph(g,ord('A')+s-7))==(not bool(rs));tests+=1
with gzip.open(A/'results.json.gz','rt') as f:source=json.load(f)
cover=json.loads((A/'source-results.json').read_text());comp=json.loads((A/'source-completion-results.json').read_text());es={(r['source_index'],j):edges for r in comp['results'] for j,edges in enumerate(r['solutions'])};results=json.loads((P/'results.json').read_text());assert results['summary']['status']=='COMPLETE';survivors=[];out=[];start=time.monotonic();deadline=start+60
assert len(results['results'])==len(source['results'])==459
for ci,(r,original) in enumerate(zip(results['results'],source['results'])):
 assert r['case_index']==ci and r['source_index']==original['source_index'] and r['singleton_index']==original['singleton_index'];codes=r['certificates'];assert len(codes)==r['visited']==r['total']==len(original['solutions']) and r['unvisited']==0
 assert set(codes)<=set('.ABCDEFGHIJKLMN') and codes.count('.')==r['survivors'] and len(codes)-codes.count('.')==r['negative']
 g=[0]*21
 def add(u,v):g[u]|=1<<v;g[v]|=1<<u
 for u,v in cover['F_edges']+es[r['source_index'],r['singleton_index']]:add(u,v)
 for s,hosts in enumerate(cover['representatives'][r['source_index']]['singleton_hosts'],7):
  for e in hosts:add(s,e)
 flat=array.array('I',(x for pair,hosts in original['solutions'] for x in pair+hosts));buf=(u32*len(flat)).from_buffer(flat);cs=(u8*len(codes)).from_buffer_copy(codes.encode());bad=ctypes.c_int(-1)
 status=lib.verify_batch((u64*21)(*g),buf,cs,len(codes),max(0,deadline-time.monotonic()),ctypes.byref(bad));assert status==1,(ci,status,bad.value)
 survivors.extend([ci,i] for i,c in enumerate(codes) if c=='.');out.append(dict(case_index=ci,checked=len(codes),negative=r['negative'],survivors=r['survivors']))
assert survivors==json.loads((P/'survivors.json').read_text())
r=dict(status='PASS',cases=len(out),checked=sum(x['checked'] for x in out),negative=sum(x['negative'] for x in out),survivors=len(survivors),fixed_graph_tests=tests,seconds=time.monotonic()-start,results=out);(P/'verification.json').write_text(json.dumps(r,indent=2)+'\n');print({k:v for k,v in r.items() if k!='results'})
