from pathlib import Path
import json,hashlib,sqlite3,ctypes,importlib.util,random,time
O=Path(__file__).parent;P=Path('/tmp/erdos85-sol1-h7-monotone-pair-host-api');start=time.monotonic()
for f,h in json.loads((P/'pins.json').read_text()).items():assert hashlib.sha256((P/f).read_bytes()).hexdigest()==h
for f,h in json.loads((P/'origins.json').read_text()).items():assert hashlib.sha256(Path(f).read_bytes()).hexdigest()==h
c=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True);c.row_factory=sqlite3.Row
for old in json.loads((P/'premises.json').read_text()):
 live=dict(c.execute('select * from review_requests where id=?',(old['id'],)).fetchone());assert live==old and live['status']=='resolved' and live['resolution'].startswith('PASS')
def module(path,name):
 spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
cv=module(O.parent/'h7-host-receipt-cover-verifier/cover.py','cover');ev=module(O.parent/'h7-monotone-host-prefix-verifier/verify.py','endpoint')
lib=ctypes.CDLL(str(O/'hosts.dylib'));lib.enumerate_hosts.argtypes=[ctypes.POINTER(ctypes.c_uint64),ctypes.c_int,ctypes.c_double];lib.enumerate_hosts.restype=ctypes.c_char_p;lib.check_fixed_hosts.argtypes=[ctypes.POINTER(ctypes.c_uint64),ctypes.POINTER(ctypes.c_uint64),ctypes.c_int,ctypes.c_double];lib.check_fixed_hosts.restype=ctypes.c_char_p

def call(base,fixed=None,cap=100000,seconds=60):
 gm=(ctypes.c_uint64*49)(*[sum(1<<v for v in ns) for ns in base])
 return json.loads(lib.enumerate_hosts(gm,cap,seconds) if fixed is None else lib.check_fixed_hosts(gm,(ctypes.c_uint64*7)(*fixed),cap,seconds))

def unhost(g):
 g=list(map(set,g));H=set(range(7));E=[u for u in range(7,49) if not g[u]&H];PV=[u for u in range(7,49) if len(g[u]&H)==2];fixed=[sum(1<<p for p in PV if p in g[e]) for e in E]
 for e in E:
  for p in PV:g[e].discard(p);g[p].discard(e)
 return g,fixed
prefixes=leafdomains=structural=0

def verify(base,r,fixed=None):
 global prefixes,leafdomains,structural
 cov=cv.check(base,r,fixed);structural+=cov['nodes']
 for prune in r['prunes']:assert ev.verify_prune(base,r['empty_vertices'],r['order'],prune);prefixes+=1
 for chosen in r['solutions']:
  g=ev.reconstruct(base,r['empty_vertices'],r['order'],7,chosen)
  for s in range(7,49):
   if len(g[s]&set(range(7)))==1:assert ev.domains(g,s);leafdomains+=1
 return cov
full=json.loads((O.parent/'h7-a6-same-colour-fixture/fixture.json').read_text())['neighbors'];base,fixed=unhost(full)
r=call(base);assert r['status']=='COMPLETE';cov=verify(base,r);(O/'unrestricted-receipt.json').write_text(json.dumps(r,indent=2)+'\n')
results=[dict(kind='unrestricted_existing_a6_fixture',nodes=r['nodes'],solutions=len(r['solutions']),prunes=len(r['prunes']),coverage=cov)]
for cap in [0,1,10,100,1000,r['nodes']-1]:
 z=call(base,cap=cap);assert z['status']=='UNKNOWN' and z['nodes']==cap+1;assert not verify(base,z)['coverage_proved']
assert call(base,cap=r['nodes'])==r
z=call(base,seconds=-1);assert z['status']=='UNKNOWN' and z['nodes']==1;verify(base,z)
rng=random.Random(2123)
fixtures=json.loads((P/'fixtures_a7.json').read_text())[:3]+json.loads((P/'fixtures_a6.json').read_text())[:3]
for fi,full in enumerate(fixtures):
 highs=list(range(7));lows=list(range(7,49));rng.shuffle(highs);rng.shuffle(lows);perm=highs+lows;adj=[[] for _ in range(49)]
 for u,ns in enumerate(full):adj[perm[u]]=[perm[v] for v in ns]
 b,f=unhost(adj);z=call(b,f);assert z['status']=='COMPLETE';verify(b,z,f)
 results.append(dict(kind='relabelled_fixed',index=fi,nodes=z['nodes'],solutions=len(z['solutions']),prunes=len(z['prunes'])))
 for cap in [0,z['nodes']-1]:
  w=call(b,f,cap=cap);assert w['status']=='UNKNOWN';verify(b,w,f)
 assert call(b,f,cap=z['nodes'])==z
bad=[set(ns) for ns in base];bad[0].add(0);assert call(bad)['status']=='INVALID_INPUT'
bad=[set(ns) for ns in base];v=next(iter(bad[0]));bad[0].remove(v);assert call(bad)['status']=='INVALID_INPUT'
bad=[set(ns) for ns in base];bad[28].add(29);bad[29].add(28);assert call(bad)['status']=='INVALID_INPUT'
out=dict(status='PASS',results=results,prefixes_replayed=prefixes,survivor_singleton_domains=leafdomains,structural_nodes=structural,seconds=time.monotonic()-start,scope='One existing a6 fixture unrestricted traversal fully independently covered; six new high/low relabel fixed-host fixtures. All prefix endpoints direct49graph-star checked, all survivor singleton domains nonempty. UNKNOWN receipts preserve verified partial results without completeness. No family launch.')
(O/'results.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
