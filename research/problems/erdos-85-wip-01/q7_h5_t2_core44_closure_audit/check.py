import pathlib,json,hashlib,collections,itertools
P=pathlib.Path(__file__).parent
load=lambda f:json.loads((P/f).read_text())
for f,v in load('origins.json').items():assert hashlib.sha256((P/f).read_bytes()).hexdigest()==v['sha256']
reviews={r['id']:r for r in load('reviews.json')}
for i,r in reviews.items():
 assert r['status']=='resolved'
 assert r['resolution'].startswith('PARTIAL' if i==2050 else 'PASS')
O=[0,4,7,11]
def key(shared,omitted,internal,af,bf):return(shared,omitted,tuple(map(tuple,internal)),af,bf)
def rk(r):return key(r['shared'],r['omitted'],r['internal'],r['af'],r['bf'])
bs=load('sharing-branches.json')['results'];sharing={rk(r) for r in bs};assert len(bs)==len(sharing)==76
assert collections.Counter(k[0] for k in sharing)=={1:40,2:36}
no={key(0,o,[[1,3]],a,b) for o,a,b in itertools.product(O,[3,4],[1,2])}
universe=sharing|no;assert len(universe)==92
assignment={}
def assign(k,review,evidence):
 assert k in universe and k not in assignment,(k,review)
 assignment[k]={'review':review,'evidence':evidence}
seen=set();initialpositive=set()
for r in load('sharing-empty.json')['results']:
 assert r['unvisited']==0
 for c in r['choices']:
  k=key(r['shared'],r['omitted'],c['internal'],c['af'],c['bf']);assert k not in seen;seen.add(k)
  if c['status']=='EXHAUSTED':assign(k,2049,'independently reviewed F-star/empty necessary projection')
  else:
   assert c['adjacency'] is not None;initialpositive.add(k)
assert seen==sharing and len(initialpositive)==12
r11=load('sharing1-omitted11.json')['results'];assert {r['omitted']:r['status'] for r in r11}=={7:'UNKNOWN',11:'EXHAUSTED'}
assign(key(1,11,[],4,2),2050,'only independently EXHAUSTED omitted11 scope of PARTIAL review')
r7=load('sharing1-omitted7.json');assert r7['status']=='COMPLETE' and r7['counts']['heavy_leaves']==r7['counts']['contradictions']==256 and r7['counts']['fixed_points']==0
assign(key(1,7,[],4,2),2059,'new complete-colour0 decomposition; old review2050 omitted7 remains UNKNOWN')
neg2=set();caps2=set()
for r in load('sharing2-integrated.json')['results']:
 assert r['unvisited']==0
 for c in r['choices']:
  k=key(2,r['omitted'],c['internal'],c['af'],c['bf'])
  assert k in initialpositive
  if c['status']=='EXHAUSTED':neg2.add(k)
  else:assert c['status']=='CAPPED';caps2.add(k)
assert len(neg2)==len(caps2)==5 and not neg2&caps2
ind=load('sharing2-five-negative-independent.json')['results'];assert len(ind)==5 and all(r['status']=='EXHAUSTED' for r in ind)
assert {key(2,r['omitted'],r['internal'],r['af'],r['bf']) for r in ind}==neg2
for k in neg2:assign(k,2051,'independent static outer/host negative')
col=load('sharing2-colour0.json')['results'];assert len(col)==5
assert {key(2,r['omitted'],r['internal'],r['af'],r['bf']) for r in col}==caps2
ci=load('sharing2-independent.json');assert ci['unvisited_branches']==0 and len(ci['results'])==5 and all(r['status']=='EXHAUSTED' for r in ci['results'])
assert {(r['omitted'],tuple(map(tuple,r['internal']))) for r in ci['results']}=={(k[1],k[2]) for k in caps2}
for k in caps2:assign(k,2058,'new complete-colour0 decomposition; historical cap unchanged')
ns=load('no-sharing-independent.json');assert ns['unvisited']==0 and len(ns['results'])==8 and all(r['status']=='EXHAUSTED' for r in ns['results'])
assert {(r['omitted'],r['f3_d3_edge']) for r in ns['results']}==set(itertools.product(O,[False,True]))
for k in no:
 if k[4]==1:assign(k,2055,'universal B-special colour2 target obstruction')
 elif k[3]==4:assign(k,2056,'universal colour0 matching four-cycle obstruction')
 else:assign(k,2061,'two own-colour normal forms exhaust for this omitted pattern')
assert set(assignment)==universe
counts=collections.Counter(a['review'] for a in assignment.values());assert counts=={2049:64,2050:1,2059:1,2051:5,2058:5,2055:8,2056:4,2061:4}
rows=[{'key':k,**a} for k,a in assignment.items()];rows.sort(key=lambda r:json.dumps(r['key']))
result={'status':'PASS','universe':92,'no_sharing':16,'shared_f1':40,'shared_f2':36,'uncovered':0,'multiply_assigned':0,'exclusions_by_review':dict(sorted(counts.items())),'rows':rows,'scope':'Conditional core44 closure accounting from accepted structural covers and separately reviewed mathematical/computational exclusions. No Lean theorem or SAT queue mutation.'}
(P/'results.json').write_text(json.dumps(result,indent=2)+'\n');print({k:v for k,v in result.items() if k!='rows'})
