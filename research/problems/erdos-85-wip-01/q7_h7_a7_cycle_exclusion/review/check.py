import pathlib,json,gzip,ctypes,itertools,hashlib,sqlite3,time,collections
P=pathlib.Path(__file__).parent;A=pathlib.Path('/tmp/erdos85-sol1-h7-projection-residual-driver');B=pathlib.Path('/tmp/erdos85-sol1-h7-projection-extension');S=P.parent/'h7-projection-singleton-shortcut-pass';read=lambda p:json.loads(p.read_text());pins=read(A/'pins.json')
for f,h in pins.items():assert hashlib.sha256((A/f).read_bytes()).hexdigest()==h
assert (A/'input-survivors.json').read_bytes()==(S/'survivors.json').read_bytes();assert (A/'source-pins.json').read_bytes()==(S/'pins.json').read_bytes()
c=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True);c.row_factory=sqlite3.Row
for f in ['premises.json','closure-premises.json']:
 for old in read(A/f):
  live=dict(c.execute('select * from review_requests where id=?',(old['id'],)).fetchone())
  for r in [old,live]:
   if isinstance(r['refs'],str):r['refs']=json.loads(r['refs'])
   r.pop('expired',None)
  assert old==live and live['resolution'].startswith('PASS')
lib=ctypes.CDLL(str(P/'templates.dylib'));U=ctypes.c_uint64;lib.domains.argtypes=[ctypes.POINTER(U),ctypes.c_int,ctypes.POINTER(U)];lib.domains.restype=ctypes.c_int
buffer=(U*1024)()
def domain(g,u):
 n=lib.domains((U*49)(*g),u,buffer);assert 0<=n<=1024;return set(buffer[:n])
# Independent explicit-template checks on the old fixtures.
fixtures=read(P.parent/'h7-singleton-complete-row-api/fixtures.json');fixed=read(P.parent/'h7-singleton-complete-row-api/receipts.json');fixedrows=0
for adj,r in zip(fixtures,fixed):
 g=[sum(1<<v for v in ns) for ns in adj]
 for u,rs in r['initial'].items():assert domain(g,int(u))==set(rs);fixedrows+=len(rs)
with gzip.open(B/'results.json.gz','rt') as f:source=json.load(f)
cover=read(B/'source-results.json');comp=read(B/'source-completion-results.json');edges={(r['source_index'],j):es for r in comp['results'] for j,es in enumerate(r['solutions'])};indices=read(A/'input-survivors.json');out=read(A/'results.json');assert out['total']==out['visited']==28908 and out['unvisited']==out['prior_unvisited']==0 and out['retained']==[]
counts=collections.Counter();cache={};seen=[];domains=rows=batches=failures=0;start=time.monotonic()
with gzip.open(A/'receipts.jsonl.gz','rt') as f:
 for line in f:
  assert time.monotonic()-start<60
  rec=json.loads(line);ci,ai=rec['case_index'],rec['assignment_index'];seen.append([ci,ai]);original=source['results'][ci];pairing,matchings=original['solutions'][ai]
  if ci not in cache:
   g=[0]*49
   def add(a,b):g[a]|=1<<b;g[b]|=1<<a
   ren=lambda u:u+42 if u<7 else u
   for a,b in cover['F_edges']+edges[original['source_index'],original['singleton_index']]:add(ren(a),ren(b))
   for u,hosts in enumerate(cover['representatives'][original['source_index']]['singleton_hosts'],7):
    for e in hosts:add(u,42+e)
   for k,(a,b) in enumerate(itertools.combinations(range(7),2),21):add(k,a);add(k,b)
   cache[ci]=g
  g=list(cache[ci])
  def add(a,b):g[a]|=1<<b;g[b]|=1<<a
  for h,d in enumerate(pairing):add(h,14+h);add(h,7+d)
  for e,m in enumerate(matchings):
   while m:
    bit=m&-m;add(42+e,21+bit.bit_length()-1);m-=bit
  cert=rec['receipt'];assert 0<cert['nodes']<=100000;counts[cert['status']]+=1
  if cert['status']=='INFEASIBLE_ROW':wanted={cert['empty_vertex']:[]}
  else:assert cert['status']=='INFEASIBLE_ARC';wanted={int(u):rs for u,rs in cert['initial'].items()};assert set(wanted)==set(range(7,42))
  for u,rs in wanted.items():assert len(rs)==len(set(rs)) and domain(g,u)==set(rs);domains+=1;rows+=len(rs)
  if cert['status']=='INFEASIBLE_ARC':
   current={u:set(rs) for u,rs in wanted.items()}
   for event in cert['events']:
    u,v=event['vertex'],event['against'];removed=set(event['removed']);assert u!=v and len(removed)==len(event['removed']) and removed<=current[u]
    for a in removed:
     for b in current[v]:assert ((a>>v)&1)!=((b>>u)&1) or ((g[u]|a)&(g[v]|b)).bit_count()>1
     failures+=1
    current[u]-=removed;batches+=1
   assert not current[cert['empty_vertex']]
assert seen==indices and dict(counts)==out['counts'];prior=read(S/'results.json')['summary'];assert prior['assignments']==1531654 and prior['negative']==1502746 and prior['survivors']==len(indices) and prior['unvisited']==0;assert 1502746+counts['INFEASIBLE_ROW']+counts['INFEASIBLE_ARC']==1531654
r=dict(status='PASS',assignments=len(indices),counts=dict(counts),domains=domains,rows=rows,batches=batches,failed_support_rows=failures,pins=len(pins),fixed_fixture_domains=1155,fixed_fixture_rows=fixedrows,seconds=time.monotonic()-start,conclusion='Entire a7 F=C7 subcase excluded by accepted2107/2110/2114 covering chain plus all checked residual endpoints. Other F,a6,H7,Lean/global remain open.')
(P/'results.json').write_text(json.dumps(r,indent=2)+'\n');print(r)
