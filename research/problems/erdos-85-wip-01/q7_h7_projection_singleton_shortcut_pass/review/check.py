import array,ctypes,gzip,hashlib,json,pathlib,sqlite3,time
P=pathlib.Path(__file__).parent;A=pathlib.Path('/tmp/erdos85-sol1-h7-projection-extension');S=pathlib.Path('/Users/rwalters/lean-genius-q7-outside-first-20260910/h7-projection-singleton-shortcut-pass')
for root in [A,S]:
    for f,h in json.loads((root/'pins.json').read_text()).items():assert hashlib.sha256((root/f).read_bytes()).hexdigest()==h
data=json.loads(gzip.decompress((A/'results.json.gz').read_bytes()));source=json.loads((A/'source-results.json').read_text());comp=json.loads((A/'source-completion-results.json').read_text())
result=json.loads((S/'results.json').read_text());survivors=json.loads((S/'survivors.json').read_text())
assert result['summary']['status']=='COMPLETE' and result['summary']['unvisited']==0
assert len(result['results'])==len(data['results'])==459
edges={(r['source_index'],j):es for r in comp['results'] for j,es in enumerate(r['solutions'])}
lib=ctypes.CDLL(str(P/'subsets.dylib'));lib.verify_batch.argtypes=[ctypes.POINTER(ctypes.c_uint64),ctypes.POINTER(ctypes.c_uint32),ctypes.POINTER(ctypes.c_uint8),ctypes.c_int,ctypes.c_double,ctypes.POINTER(ctypes.c_int),ctypes.POINTER(ctypes.c_uint64),ctypes.POINTER(ctypes.c_int)];lib.verify_batch.restype=ctypes.c_int
start=time.monotonic();total=ctypes.c_uint64();maxnodes=ctypes.c_int();bad=ctypes.c_int();expected=[];negative=0;tested=0;mutations=0
for ci,(r,a) in enumerate(zip(data['results'],result['results'])):
    assert a['case_index']==ci and a['source_index']==r['source_index'] and a['singleton_index']==r['singleton_index']
    codes=a['certificates'];assert len(codes)==a['visited']==a['total']==len(r['solutions']) and a['unvisited']==0
    assert a['survivors']==codes.count('.') and a['negative']==len(codes)-codes.count('.')
    expected.extend([ci,i] for i,c in enumerate(codes) if c=='.');negative+=a['negative'];tested+=len(codes)
    g=[0]*21
    all_edges=source['F_edges']+edges[r['source_index'],r['singleton_index']]+[[e,s] for s,h in enumerate(source['representatives'][r['source_index']]['singleton_hosts'],7) for e in h]
    for u,v in all_edges:g[u]|=1<<v;g[v]|=1<<u
    base=(ctypes.c_uint64*21)(*g);flat=array.array('I',(v for p,ms in r['solutions'] for v in p+ms));records=(ctypes.c_uint32*len(flat)).from_buffer(flat);encoded=(ctypes.c_uint8*len(codes))(*codes.encode())
    assert lib.verify_batch(base,records,encoded,len(codes),60-(time.monotonic()-start),ctypes.byref(bad),ctypes.byref(total),ctypes.byref(maxnodes))==1,(ci,bad.value)
    if mutations==0 and codes and codes[0]!='.':
        altered=(ctypes.c_uint8*1)(ord('.'));dummy=ctypes.c_uint64();mx=ctypes.c_int()
        assert lib.verify_batch(base,records,altered,1,1,ctypes.byref(bad),ctypes.byref(dummy),ctypes.byref(mx))==0
        invalid=(ctypes.c_uint8*1)(ord('Z'))
        assert lib.verify_batch(base,records,invalid,1,1,ctypes.byref(bad),ctypes.byref(dummy),ctypes.byref(mx))==0
        mutations=2
assert expected==survivors and tested==result['summary']['visited']==1531654 and negative==1502746 and len(survivors)==28908
db=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True);db.row_factory=sqlite3.Row;premises=[]
for rid in [2110,2113]:
    r=dict(db.execute('select * from review_requests where id=?',(rid,)).fetchone());assert r['status']=='resolved' and r['resolution'].startswith('PASS');premises.append(r)
(P/'premises.json').write_text(json.dumps(premises,indent=2)+'\n')
out=dict(status='PASS',cases=459,assignments=tested,negative=negative,survivors=len(survivors),nodes=total.value,max_nodes=maxnodes.value,mutations_rejected=mutations,seconds=time.monotonic()-start)
(P/'results.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
