import pathlib,json,itertools,hashlib,sqlite3,collections
P=pathlib.Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3/core44-closure-audit');load=lambda f:json.loads((P/f).read_text())
for f,h in load('pins.json').items():assert hashlib.sha256((P/f).read_bytes()).hexdigest()==h
for f,origin in load('origins.json').items():assert (P/f).read_bytes()==pathlib.Path(origin['path']).read_bytes() and hashlib.sha256((P/f).read_bytes()).hexdigest()==origin['sha256']
db=sqlite3.connect('/Users/rwalters/GitHub/lean-genius/.squad/squad.db');db.row_factory=sqlite3.Row
for r in load('reviews.json'):
 current=dict(db.execute('select * from review_requests where id=?',(r['id'],)).fetchone());current['refs']=json.loads(current['refs']);current['expired']=False;assert current==r
 assert r['status']=='resolved' and r['resolution'].startswith('PARTIAL' if r['id']==2050 else 'PASS')
O=[0,4,7,11];universe=set()
for o,a,b in itertools.product(O,[3,4],[1,2]):universe.add((0,o,((1,3),),a,b))
for shared in [1,2]:
 internals=[(),((0,1),),((0,3),)]+([((1,3),)] if shared==2 else [])
 for internal,o,a,b in itertools.product(internals,O,[None,3,4],[None,1,2]):
  partner=next((v for u,v in internal if u==0),None)
  if partner is None and (a is None or b is None):continue
  if a is None and b is None:continue
  if b==shared:continue
  if partner is not None and partner in [a,b]:continue
  universe.add((shared,o,internal,a,b))
def key(s,o,c):return (s,o,tuple(map(tuple,c['internal'])),c['af'],c['bf'])
sharing={key(r['shared'],r['omitted'],r) for r in load('sharing-branches.json')['results']}
assert sharing=={k for k in universe if k[0]} and len(universe)==92
initial={key(r['shared'],r['omitted'],c):c for r in load('sharing-empty.json')['results'] for c in r['choices']};assert set(initial)==sharing
integrated={key(2,r['omitted'],c):c for r in load('sharing2-integrated.json')['results'] for c in r['choices']}
confirmed5={key(2,r['omitted'],r) for r in load('sharing2-five-negative-independent.json')['results'] if r['status']=='EXHAUSTED'}
colour0={key(2,r['omitted'],r) for r in load('sharing2-colour0.json')['results']}
independent0={(r['omitted'],tuple(map(tuple,r['internal']))) for r in load('sharing2-independent.json')['results'] if r['status']=='EXHAUSTED'}
assert len(independent0)==len(colour0)==5 and independent0=={(k[1],k[2]) for k in colour0}
scope2050={r['omitted']:r['status'] for r in load('sharing1-omitted11.json')['results']};assert scope2050=={7:'UNKNOWN',11:'EXHAUSTED'}
scope2059=load('sharing1-omitted7.json');assert scope2059['status']=='COMPLETE' and scope2059['counts']['heavy_leaves']==scope2059['counts']['contradictions']==256 and scope2059['counts']['fixed_points']==0
normal={(r['omitted'],r['f3_d3_edge']) for r in load('no-sharing-independent.json')['results'] if r['status']=='EXHAUSTED'};assert normal==set(itertools.product(O,[False,True]))
assigned={}
for k in universe:
 s,o,internal,a,b=k
 if s==0:rid=2055 if b==1 else 2056 if a==4 else 2061
 elif initial[k]['status']=='EXHAUSTED':rid=2049
 else:
  assert initial[k]['status']=='PARTIAL_WITNESS'
  if s==1:
   assert internal==() and (a,b)==(4,2) and o in [7,11];rid=2050 if o==11 else 2059
  elif k in confirmed5:assert integrated[k]['status']=='EXHAUSTED';rid=2051
  else:assert integrated[k]['status']=='CAPPED' and k in colour0;rid=2058
 assigned[k]=rid
author={tuple([r['key'][0],r['key'][1],tuple(map(tuple,r['key'][2])),r['key'][3],r['key'][4]]):r['review'] for r in load('results.json')['rows']}
assert author==assigned
counts=dict(collections.Counter(assigned.values()));assert counts=={2049:64,2050:1,2059:1,2051:5,2058:5,2055:8,2056:4,2061:4}
out=dict(status='PASS',branches=92,counts=counts,method='Independent branch-key reconstruction from reciprocal colour0 target restrictions; independent endpoint dispatch and exact author-row comparison',source_copies='all identical to original pinned sources',reviews='all12 snapshots exactly match live resolved records',scope='Complete conditional core44 cover/exclusion accounting only; no Lean or queue claim')
print(out);pathlib.Path(__file__).with_name('REVIEW2063.json').write_text(json.dumps(out,indent=2)+'\n')
