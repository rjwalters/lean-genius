import collections,ctypes,gzip,json,pathlib,time
P=pathlib.Path(__file__).parent;A=pathlib.Path('/tmp/erdos85-sol1-h7-projection-extension')
data=json.loads(gzip.decompress((A/'results.json.gz').read_bytes()));source=json.loads((A/'source-results.json').read_text());comp=json.loads((A/'source-completion-results.json').read_text())
edges={(r['source_index'],j):es for r in comp['results'] for j,es in enumerate(r['solutions'])}
indices=json.loads((P/'input-survivors.json').read_text());out=json.loads((P/'results.json').read_text())
assert out['total']==out['visited']==len(indices)==28908 and out['unvisited']==out['prior_unvisited']==0 and not out['retained']
lib=ctypes.CDLL(str(P/'subsets.dylib'));lib.verify_domain.argtypes=[ctypes.POINTER(ctypes.c_uint64),ctypes.c_int,ctypes.POINTER(ctypes.c_uint64),ctypes.c_int,ctypes.c_int,ctypes.c_double,ctypes.POINTER(ctypes.c_int)];lib.verify_domain.restype=ctypes.c_int
counts=collections.Counter();cache={};seen=[];nodes=domains=rows=batches=failures=0;maxnodes=0;start=time.monotonic()
with gzip.open(P/'receipts.jsonl.gz','rt') as f:
 for line in f:
    receipt=json.loads(line);ci,ai=receipt['case_index'],receipt['assignment_index'];seen.append([ci,ai]);r=data['results'][ci];p,ms=r['solutions'][ai]
    if ci not in cache:
        g=[0]*49
        def add(a,b):g[a]|=1<<b;g[b]|=1<<a
        def ren(a):return 42+a if a<7 else a
        for a,b in source['F_edges']+edges[r['source_index'],r['singleton_index']]:add(ren(a),ren(b))
        for s,hosts in enumerate(source['representatives'][r['source_index']]['singleton_hosts'],7):
            for e in hosts:add(s,42+e)
        k=21
        for a in range(7):
            for b in range(a+1,7):add(k,a);add(k,b);k+=1
        cache[ci]=g
    g=list(cache[ci])
    def add(a,b):g[a]|=1<<b;g[b]|=1<<a
    for h,d in enumerate(p):add(h,14+h);add(h,7+d)
    for e,m in enumerate(ms):
        while m:
            bit=m&-m;add(42+e,21+bit.bit_length()-1);m-=bit
    gm=(ctypes.c_uint64*49)(*g);used=ctypes.c_int();cert=receipt['receipt'];counts[cert['status']]+=1
    assert 0<cert['nodes']<=100000
    if cert['status']=='INFEASIBLE_ROW':wanted={cert['empty_vertex']:[]}
    else:
        assert cert['status']=='INFEASIBLE_ARC'
        wanted={int(u):rs for u,rs in cert['initial'].items()};assert set(wanted)==set(range(7,42))
    for u,rs in wanted.items():
        assert 7<=u<42
        expected=(ctypes.c_uint64*len(rs))(*rs)
        assert lib.verify_domain(gm,u,expected,len(rs),100000,60-(time.monotonic()-start),ctypes.byref(used))==1,(ci,ai,u,used.value)
        domains+=1;rows+=len(rs)
    nodes+=used.value;maxnodes=max(maxnodes,used.value)
    if cert['status']=='INFEASIBLE_ARC':
        current={u:set(rs) for u,rs in wanted.items()}
        for event in cert['events']:
            u,v=event['vertex'],event['against'];removed=event['removed'];assert len(removed)==len(set(removed)) and set(removed)<=current[u] and u!=v
            for a in removed:
                for b in current[v]:assert ((a>>v)&1)!=((b>>u)&1) or ((g[u]|a)&(g[v]|b)).bit_count()>1
                failures+=1
            current[u]-=set(removed);batches+=1
        assert not current[cert['empty_vertex']]
assert seen==indices and dict(counts)==out['counts']
result=dict(status='PASS',assignments=len(seen),counts=dict(counts),domains=domains,rows=rows,batches=batches,failed_support_rows=failures,nodes=nodes,max_nodes=maxnodes,seconds=time.monotonic()-start)
(P/'verification.json').write_text(json.dumps(result,indent=2)+'\n');print(result)
