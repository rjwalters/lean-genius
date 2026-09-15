import gzip,hashlib,itertools,json,sqlite3,time
from pathlib import Path
P=Path('/Users/rwalters/lean-genius-h7-a6-f16-sol2-20260915');O=Path(__file__).parent
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins=read(P/'input-pins.json')
for n,h in pins.items():assert sha(P/n)==h
l=read(P/'inputs-launch.json');A=Path(l['source_path']);Q=Path(l['quotient_path'])
assert sha(A/'pins.json')==l['source_pins_sha256'] and sha(Q/'pins.json')==l['quotient_pins_sha256'] and sha(P/'inputs.py')==l['driver_sha256']
for d in [A,Q]:
 for n,h in read(d/'pins.json').items():assert sha(d/n)==h
c=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True)
for rid in [2118,2122,2125]:
 st,res=c.execute('select status,resolution from review_requests where id=?',(rid,)).fetchone();assert st=='resolved' and res.startswith('PASS')
start=time.monotonic();F=read(A/'source-cover-results.json')['cases'];C=read(A/'source-completion-results.json')['results'];layout=read(Q/'source-layout.json')
H={}
for line in gzip.open(A/'high-colourings.jsonl.gz','rt'):
 h=json.loads(line)
 if h['F_index']==16:H[h['completion_index'],h['singleton_index']]=h
slice_ids={r['completion_index'] for r in layout if r['F_index']==16}
reps=[r for r in read(Q/'representatives.json') if r['completion_index'] in slice_ids]
assert len(reps)==48759 and sum(r['orbit_size'] for r in reps)==62985
assert len(H)==105 and sum(r['F_index']==16 for r in C)==44
assert slice_ids=={i for i,r in enumerate(C) if r['F_index']==16 and r['solutions']}
with gzip.open(P/'inputs.jsonl.gz','rt') as stream:
 for r in reps:
  assert time.monotonic()-start<90
  d=json.loads(next(stream));assert all(d[k]==r[k] for k in ['global_index','completion_index','singleton_index','colouring_index'])
  ci,j=r['completion_index'],r['singleton_index'];src=C[ci];assert src['F_index']==16 and src['status']=='COMPLETE'
  h=H[ci,j];assert h['status']=='COMPLETE';f=F[16];x=f['representatives'][src['X_index']];g=[0]*49
  def add(u,v):assert u!=v;g[u]|=1<<v;g[v]|=1<<u
  ren=lambda u:u+42 if u<7 else u
  for u,v in f['F_edges']+src['solutions'][j]:add(ren(u),ren(v))
  for u,es in enumerate(x['singleton_hosts'],7):
   for e in es:add(u,42+e)
  for v,(u,w) in enumerate(itertools.combinations(range(7),2),21):add(v,u);add(v,w)
  for u,v in enumerate(h['colourings'][r['colouring_index']],7):add(u,v)
  for u in range(3):add(u,18+u)
  assert len(d['neighbors'])==49
  assert all(ns==sorted(set(ns)) and sum(1<<v for v in ns)==g[u] for u,ns in enumerate(d['neighbors']))
 assert next(stream,None) is None
perm=[2,3,4,0,1,6,5];mask=622659
assert {tuple(sorted((perm[u],perm[v]))) for i,(u,v) in enumerate(itertools.combinations(range(7),2)) if mask>>i&1}==set(map(tuple,F[16]['F_edges']))
report=read(P/'input-verification.json');assert report['input_sha256']==sha(P/'inputs.jsonl.gz') and report['seconds']<l['aggregate_seconds']==60
assert report['global_indices']==[r['global_index'] for r in reps]
for n,h in pins.items():assert sha(P/n)==h
out={'status':'PASS_REVIEW2699','graphs':len(reps),'raw_highs':62985,'seconds':time.monotonic()-start,'input_manifest_sha256':sha(P/'input-pins.json'),'root':'cube_F6_t15','mask':mask,'permutation':perm,'scope':'Exact accepted source and quotient slice reconstructed via bit adjacency; no host/residual exclusion.'}
(O/'REVIEW.json').write_text(json.dumps(out,indent=2)+'\n');(O/'pins.json').write_text(json.dumps({n:sha(O/n) for n in ['audit.py','REVIEW.json']},indent=2)+'\n');print(out)
