import pathlib,json,gzip,ctypes,hashlib,sqlite3,time,collections
P=pathlib.Path(__file__).parent;A=pathlib.Path('/tmp/erdos85-sol1-h7-a6-f12-residual-pass');S=pathlib.Path('/tmp/erdos85-sol1-h7-a6-f12-host-pass')
def read(p):return json.loads(p.read_text())
for f,h in read(A/'final-pins.json').items():assert hashlib.sha256((A/f).read_bytes()).hexdigest()==h
for f,h in read(S/'pins.json').items():assert hashlib.sha256((S/f).read_bytes()).hexdigest()==h
assert (A/'source-pins.json').read_bytes()==(S/'pins.json').read_bytes()
assert (A/'input-survivors.json').read_bytes()==(S/'survivors.json').read_bytes()
db=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True);db.row_factory=sqlite3.Row
for old in read(A/'premises.json'):
 live=dict(db.execute('select * from review_requests where id=?',(old['id'],)).fetchone());assert old==live and old['status']=='resolved' and old['resolution'].startswith('PASS')
inputs={r['global_index']:[sum(1<<v for v in ns) for ns in r['neighbors']] for r in map(json.loads,gzip.open(S/'inputs.jsonl.gz','rt'))}
hosts={};export=[]
for shard in read(S/'results.json')['shards']:
 for line in gzip.open(S/shard,'rt'):
  r=json.loads(line);cert=r['receipt'];assert cert['status']=='COMPLETE' and cert['empty_vertices']==list(range(42,49))
  if cert['solutions']:hosts[r['global_index']]=cert['solutions']
indices=[[g,j] for g,hs in hosts.items() for j in range(len(hs))];assert indices==read(A/'input-survivors.json')
lib=ctypes.CDLL(str(P/'templates.dylib'));U=ctypes.c_uint64;lib.domains.argtypes=[ctypes.POINTER(U),ctypes.c_int,ctypes.POINTER(U)];lib.domains.restype=ctypes.c_int
buffer=(U*1024)()
def domain(ga,u):
 n=lib.domains(ga,u,buffer);assert 0<=n<=1024;return set(buffer[:n])
summary=read(A/'results.json');assert summary['total']==397234 and summary['visited']==395764 and summary['unvisited']==1470 and summary['retained']==[[227088,0,'UNKNOWN']]
frontier=read(A/'frontier.json');unknown=[]
start=time.monotonic();seen=[];counts=collections.Counter();domains=rows=batches=failures=0
for shard in summary['shards']:
 for line in gzip.open(A/shard,'rt'):
  rec=json.loads(line);gid,li=rec['global_index'],rec['leaf_index'];seen.append([gid,li]);assert seen[-1]==indices[len(seen)-1]
  cert=rec['receipt'];assert 0<cert['nodes']<=100000;counts[cert['status']]+=1
  if cert['status']=='UNKNOWN':unknown.append(rec);continue
  g=list(inputs[gid])
  for e,m in enumerate(hosts[gid][li],42):
   g[e]|=m
   while m:
    bit=m&-m;m-=bit;g[bit.bit_length()-1]|=1<<e
  ga=(U*49)(*g)
  if cert['status']=='INFEASIBLE_ROW':wanted={cert['empty_vertex']:[]}
  else:assert cert['status']=='INFEASIBLE_ARC';wanted={int(u):rs for u,rs in cert['initial'].items()};assert set(wanted)==set(range(7,42))
  for u,rs in wanted.items():assert 7<=u<42 and len(rs)==len(set(rs)) and domain(ga,u)==set(rs);domains+=1;rows+=len(rs)
  if cert['status']=='INFEASIBLE_ARC':
   current={u:set(rs) for u,rs in wanted.items()}
   for event in cert['events']:
    u,v=event['vertex'],event['against'];removed=set(event['removed']);assert u!=v and len(removed)==len(event['removed']) and removed<=current[u]
    for a in removed:
     for b in current[v]:assert ((a>>v)&1)!=((b>>u)&1) or ((g[u]|a)&(g[v]|b)).bit_count()>1
     failures+=1
    current[u]-=removed;batches+=1
   assert not current[cert['empty_vertex']]
  assert time.monotonic()-start<60
assert seen==indices[:summary['visited']] and dict(counts)==summary['counts']
assert frontier['unknown']==unknown and frontier['unvisited']==indices[len(seen):] and frontier['visited']==len(seen) and frontier['source_total']==len(indices)
result=dict(status='PASS',negative_endpoints=len(seen)-len(unknown),unknown_preserved=len(unknown),unvisited_preserved=summary['unvisited'],counts=dict(counts),domains=domains,rows=rows,arc_batches=batches,failed_support_rows=failures,seconds=time.monotonic()-start,scope='Exact accepted2130 ordered host prefix; independent explicit-support template domains and ARC event replay of negatives only. UNKNOWN and unvisited suffix preserved; no search restart or F12 exclusion.')
(P/'results.json').write_text(json.dumps(result,indent=2)+'\n')
(P/'input-pins.json').write_text(json.dumps(read(A/'final-pins.json'),indent=2)+'\n');print(result)
