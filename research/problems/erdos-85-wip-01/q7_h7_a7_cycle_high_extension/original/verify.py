"""Independent permutation + reverse-empty product audit of terminal cases."""
import itertools,json,pathlib,time,ctypes,array,gzip
P=pathlib.Path(__file__).parent
K=list(itertools.combinations(range(7),2))
def main():
    source=json.loads((P/'source-results.json').read_text());comp=json.loads((P/'source-completion-results.json').read_text());out=json.loads(gzip.decompress((P/'results.json.gz').read_bytes()))
    originals={(r['source_index'],j):es for r in comp['results'] for j,es in enumerate(r['solutions'])}
    assert len(originals)==459 and len(out['results'])==459
    assert [(r['source_index'],r['singleton_index']) for r in out['results']]==list(originals)
    lib=ctypes.CDLL(str(P/'graphs.dylib'));lib.verify_graphs.argtypes=[ctypes.POINTER(ctypes.c_uint64),ctypes.POINTER(ctypes.c_uint32),ctypes.c_int];lib.verify_graphs.restype=ctypes.c_int
    start=time.monotonic();states=0;graphs=0;paired=0;case_results=[]
    for r in out['results']:
        assert r['status']=='COMPLETE', 'Do not retry UNKNOWN'
        x,j=r['source_index'],r['singleton_index'];hosts=source['representatives'][x]['singleton_hosts']
        edges=source['F_edges']+originals[x,j]+[[e,s] for s,h in enumerate(hosts,7) for e in h]
        g=[set() for _ in range(21)]
        for a,b in edges:g[a].add(b);g[b].add(a)
        nodes=0
        def tick():
            nonlocal nodes,states
            nodes+=1;states+=1
            assert nodes<=100000 and time.monotonic()-start<60
        found=[]
        for p in itertools.permutations(range(7)):
            tick()
            if all(7+p[i] not in g[14+i] and len(g[7+p[i]]&g[14+i])==0 for i in range(7)):found.append(p)
        assert set(found)=={tuple(p) for p in r['pairings']}
        paired+=len(found);sol=set()
        for p in found:
            colour={14+i:i for i in range(7)}|{7+d:i for i,d in enumerate(p)}
            opts=[]
            for e in range(7):
                missing=set(range(7))-{colour[s] for s in g[e] if s>=7}
                local=[]
                for a,b in itertools.combinations(range(21),2):
                    if set(K[a]).isdisjoint(K[b]) and set(K[a]+K[b])==missing:local.append((1<<a)|(1<<b))
                assert len(local)==3;opts.append(local)
            frontier=[(0,())]
            for e in reversed(range(7)):
                nxt=[]
                for used,ms in frontier:
                    for m in opts[e]:
                        tick()
                        if used&m==0:nxt.append((used|m,(m,)+ms))
                frontier=nxt
            for used,ms in frontier:
                sol.add((p,ms))
        encoded=[(tuple(p),tuple(ms)) for p,ms in r['solutions']]
        assert len(encoded)==len(set(encoded)) and sol==set(encoded)
        flat=array.array('I',(v for p,ms in encoded for v in p+ms));assert flat.itemsize==4
        recs=(ctypes.c_uint32*len(flat)).from_buffer(flat)
        bg=(ctypes.c_uint64*21)(*(sum(1<<v for v in ns) for ns in g))
        assert lib.verify_graphs(bg,recs,len(encoded))==1
        graphs+=len(encoded)
        case_results.append(dict(source_index=x,singleton_index=j,nodes=nodes,pairings=len(found),solutions=len(sol)))
    result=dict(status='PASS',cases=len(case_results),pairings=paired,graphs=graphs,states=states,seconds=time.monotonic()-start,results=case_results)
    (P/'verification.json').write_text(json.dumps(result,indent=2)+'\n');print({k:v for k,v in result.items() if k!='results'})
if __name__=='__main__':main()
