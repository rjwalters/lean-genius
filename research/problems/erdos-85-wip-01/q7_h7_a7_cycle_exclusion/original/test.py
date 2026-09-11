import array,ctypes,importlib.util,itertools,json,pathlib,time
P=pathlib.Path(__file__).parent;A=pathlib.Path('/tmp/erdos85-sol1-h7-singleton-complete-native-api')
spec=importlib.util.spec_from_file_location('reference',A/'reference.py');ref=importlib.util.module_from_spec(spec);spec.loader.exec_module(ref)
lib=ctypes.CDLL(str(P/'batch.dylib'));lib.batch_check.argtypes=[ctypes.POINTER(ctypes.c_uint64),ctypes.POINTER(ctypes.c_uint32),ctypes.c_int,ctypes.c_int,ctypes.c_double];lib.batch_check.restype=ctypes.c_char_p
K=list(itertools.combinations(range(7),2))
def call(base,record,cap,deadline,n=1):
    flat=array.array('I',record*n)
    raw=lib.batch_check((ctypes.c_uint64*21)(*base),(ctypes.c_uint32*len(flat)).from_buffer(flat),n,cap,deadline)
    result=json.loads(raw)
    for r in result:
        for key in ['initial','remaining']:
            if key in r:r[key]={int(k):v for k,v in r[key].items()}
    return result
def main():
    fixtures=json.loads((A/'fixtures.json').read_text());count=0
    for adj in fixtures:
        g=[set(ns) for ns in adj];H=set(range(7));sup=[ns&H for ns in g];E=sorted(u for u in range(7,49) if not sup[u]);S=[u for u in range(7,49) if len(sup[u])==1]
        double=sorted(s for s in S if len(g[s]&set(E))==2);single=sorted((next(iter(sup[s])),s) for s in S if len(g[s]&set(E))==1)
        rename={h:h for h in H}|{e:42+i for i,e in enumerate(E)}|{s:7+i for i,s in enumerate(double)}|{s:14+h for h,s in single}
        rename.update({u:21+K.index(tuple(sorted(sup[u]))) for u in range(7,49) if len(sup[u])==2})
        canonical=[set() for _ in range(49)]
        for u in range(49):canonical[rename[u]]={rename[v] for v in g[u]}
        pair=[next(d for d,s in enumerate(double) if h in sup[s]) for h in range(7)]
        masks=[sum(1<<(v-21) for v in canonical[42+e] if 21<=v<42) for e in range(7)]
        base=[]
        for u in range(21):
            real=u+42 if u<7 else u
            base.append(sum(1<<(v-42 if v>=42 else v) for v in canonical[real] if v>=42 or 7<=v<21))
        record=pair+masks;full=ref.check(canonical)
        for cap in [0,1,full['nodes']-1,full['nodes'],100000]:
            expected=ref.check(canonical,max_nodes=cap)
            if expected['status']=='INFEASIBLE_ROW':expected={k:expected[k] for k in ['status','empty_vertex','nodes']}
            assert call(base,record,cap,time.monotonic()+60)==[expected]
            count+=1
        assert call(base,record,100000,time.monotonic()-1)==[]
        assert len(call(base,record,0,time.monotonic()+60,2))==2
    result=dict(status='PASS',fixtures=len(fixtures),comparisons=count,expired_batches=len(fixtures),two_case_zero_caps=len(fixtures))
    (P/'test-results.json').write_text(json.dumps(result,indent=2)+'\n');print(result)
if __name__=='__main__':main()
