import ctypes,json,pathlib,time
import reference,native
P=pathlib.Path(__file__).parent;lib=ctypes.CDLL(str(P/'subsets.dylib'))
lib.verify_domain.argtypes=[ctypes.POINTER(ctypes.c_uint64),ctypes.c_int,ctypes.POINTER(ctypes.c_uint64),ctypes.c_int,ctypes.c_int,ctypes.c_double,ctypes.POINTER(ctypes.c_int)];lib.verify_domain.restype=ctypes.c_int
start=time.monotonic();domains=rows=nodes=0
for adjacency in json.loads((P/'fixtures.json').read_text()):
 g,support,E,U=reference.validate(adjacency);allrows=reference.complete_domains(g,support,U,reference.Budget(100000,time.monotonic()+60));assert allrows['status']=='DOMAINS_COMPLETE'
 assert sum((g[e]&sum(1<<v for v in E)).bit_count() for e in E)==12
 assert sum(any(support[v]==support[u] for v in range(7,49) if g[u]>>v&1) for u in U)>=2
 used=ctypes.c_int();gm=(ctypes.c_uint64*49)(*g)
 for u,rs in allrows['initial'].items():
  assert lib.verify_domain(gm,u,(ctypes.c_uint64*len(rs))(*rs),len(rs),100000,60-(time.monotonic()-start),ctypes.byref(used))==1
  domains+=1;rows+=len(rs)
 nodes+=used.value
old=json.loads(pathlib.Path('/tmp/erdos85-sol1-h7-singleton-complete-native-api/fixtures.json').read_text())[0]
for api in [native,reference]:
 try:api.check(old);raise AssertionError('a7 accepted as a6')
 except ValueError:pass
out=dict(status='PASS',domains=domains,rows=rows,nodes=nodes,a7_rejections=2,seconds=time.monotonic()-start)
(P/'independent-results.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
