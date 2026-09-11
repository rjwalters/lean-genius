from pathlib import Path
import json,itertools as it,time,hashlib,sqlite3
b=Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3');p=b/'residual-ten-D5-five-311-high-matchings';o=Path(__file__).parent
def read(p):return json.loads(p.read_text())
nh=0
for name in ['pins.json','input-pins.json']:
 if not (p/name).exists():continue
 for k,v in read(p/name).items():
  q=Path(k);q=q if q.is_absolute() else p/q
  assert hashlib.sha256(q.read_bytes()).hexdigest()==v;nh+=1
c=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True)
for rid in [2460,2463,2464]:
 s,r=c.execute('select status,resolution from review_requests where id=?',(rid,)).fetchone();assert s=='resolved' and r.startswith('PASS')
data=read(p/'results.json');alloc=read(b/'residual-ten-D5-five-311-allocation/results.json')['records'];pack=read(b/'residual-ten-D5-five-311-packing/results.json')['records'];domain=read(b/'residual-ten-D5-supports/results.json')['records']
assert data['status']=='COMPLETE'
source={(r['root'],r['class'],r['source_root']) for r in alloc if r['status']=='EXACT_RATIONAL_WITNESS'}
assert len(data['records'])==len(source)==3024 and {(r['root'],r['class'],r['source_root']) for r in data['records']}==source
start=time.monotonic();status='INCOMPLETE';total=kept=0
def guard():
 if time.monotonic()-start>30:raise TimeoutError
def ordinary(rem):
 if not rem:yield ();return
 v=rem[0]
 yield from ordinary(rem[1:])
 for j,w in enumerate(rem[1:],1):
  for edges in ordinary(rem[1:j]+rem[j+1:]):yield ((v,w),)+edges
try:
 candidates=[]
 for e in ordinary(tuple(range(10))):
  guard();e=frozenset(e)
  if frozenset(tuple(sorted((v^1,w^1))) for v,w in e)==e:candidates.append(tuple(sorted(e)))
 assert len(candidates)==312
 for rec in data['records']:
  guard();assert rec['status']=='COMPLETE';ci=rec['class'];root=pack[ci]['survivors'][rec['source_root']];d=domain[ci]
  S=[]
  for j in root['high3']:
   s=d['high3'][j];S.extend([set(s),{v^1 for v in s}])
  rho={a:z for a,z in d['edges']}|{z:a for a,z in d['edges']}
  low=[8-sum(e in s for s in S) for e in range(10)];q=root['q'];assert min(low)>0
  # Direct common-neighbor testing with one proposed high edge establishes its allowance.
  base=[0]*20
  def edge(N,a,z):N[a]|=1<<z;N[z]|=1<<a
  for a,z in d['edges']:edge(base,a,z)
  for v,s in enumerate(S):
   for a in s:edge(base,10+v,a)
  allowed=set()
  for v,w in it.combinations(range(10),2):
   N=base[:];edge(N,10+v,10+w)
   if all((N[a]&N[z]).bit_count()<=1 for a,z in it.combinations(range(20),2)):allowed.add((v,w))
  expected={};nm=0
  for edges in candidates:
   if not all(e in allowed for e in edges):continue
   nm+=1;N=base[:];partner={}
   for v,w in edges:edge(N,10+v,10+w);partner[v]=w;partner[w]=v
   assert all((N[a]&N[z]).bit_count()<=1 for a,z in it.combinations(range(20),2))
   ds=[];covers=[]
   for v in range(10):
    cover={rho[a] for a in S[v]}
    if v in partner:cover|=S[partner[v]]
    covers.append(cover);missing=set(range(10))-cover
    # Choose singleton-low endpoints first; defects are their complement.
    low_count=4 if v in partner else 5
    choices=[]
    for occupied in it.combinations(sorted(missing),low_count):
     defect=missing-set(occupied)
     if all(q[e]>0 for e in defect):choices.append(sum(1<<e for e in defect))
    ds.append(tuple(sorted(choices)))
   if any(not x for x in ds):continue
   forcedQ=[sum(all(m&(1<<e) for m in row) for row in ds) for e in range(10)]
   forcedLow=[sum(e not in covers[v] and all(not(m&(1<<e)) for m in ds[v]) for v in range(10)) for e in range(10)]
   if any(forcedQ[e]>q[e] or forcedLow[e]>low[e] for e in range(10)):continue
   expected[edges]=tuple(ds)
  actual={tuple(sorted(tuple(sorted(e)) for e in r['edges'])):tuple(tuple(sorted(row)) for row in r['Q_domains']) for r in rec['survivors']}
  assert len(actual)==len(rec['survivors']) and actual==expected and nm==rec['matchings']
  total+=nm;kept+=len(expected)
 assert (total,kept)==(37408,30256)
 status='COMPLETE'
except TimeoutError:pass
result={'status':status,'original_cap_seconds':30,'seconds':time.monotonic()-start,'hashes':nh,'allowed_matchings':total,'surviving_matchings':kept}
(o/'audit.json').write_text(json.dumps(result,indent=2)+'\n');print(result)
