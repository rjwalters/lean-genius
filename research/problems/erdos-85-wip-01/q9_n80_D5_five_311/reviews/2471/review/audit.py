from pathlib import Path
import json,itertools as it,hashlib,sqlite3,time,math
b=Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3');o=Path(__file__).parent
def read(f):return json.loads(f.read_text())
nh=0
for folder in ['residual-ten-D5-five-311-empty-high-joint','residual-ten-D5-five-311-empty-high-low-balance']:
 p=b/folder
 for name in ['pins.json','input-pins.json']:
  if not (p/name).exists():continue
  for k,v in read(p/name).items():
   q=Path(k);q=q if q.is_absolute() else p/q
   assert hashlib.sha256(q.read_bytes()).hexdigest()==v;nh+=1
c=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True)
for rid in [2460,2463,2464,2467,2468,2469]:
 s,r=c.execute('select status,resolution from review_requests where id=?',(rid,)).fetchone();assert s=='resolved' and r.startswith('PASS')
joint=read(b/'residual-ten-D5-five-311-empty-high-joint/results.json');lowres=read(b/'residual-ten-D5-five-311-empty-high-low-balance/results.json');assert joint['status']==lowres['status']=='COMPLETE'
alloc=read(b/'residual-ten-D5-five-311-fixed-allocation/results.json')['records'];high={r['root']:r for r in read(b/'residual-ten-D5-five-311-high-matchings/results.json')['records']};pack=read(b/'residual-ten-D5-five-311-packing/results.json')['records'];dom=read(b/'residual-ten-D5-supports/results.json')['records']
source={r['root']:r for r in alloc if r['status']=='EXACT_RATIONAL_WITNESS' and not high[r['packing_root']]['survivors'][r['graph']]['edges']}
jm={r['root']:r for r in joint['records']};lm={r['root']:r for r in lowres['records']};assert jm.keys()==lm.keys()==source.keys() and len(jm)==len(joint['records'])==len(lm)==len(lowres['records'])==24
start=time.monotonic();status='INCOMPLETE';raw=solcount=negative=0;pairs=list(it.combinations(range(10),2))
def guard():
 if time.monotonic()-start>30:raise TimeoutError
def flip(m):return sum(1<<(v^1) for v in range(10) if m&(1<<v))
try:
 for key,src in source.items():
  guard();saved=jm[key];ci=src['class'];root=pack[ci]['survivors'][src['source_root']];d=dom[ci];g=high[src['packing_root']]['survivors'][src['graph']]
  for field in ['class','source_root','packing_root','graph']:assert saved[field]==src[field]
  rho={v:w for a,z in d['edges'] for v,w in [(a,z),(z,a)]};S=[]
  for index in root['high3']:
   s=set(d['high3'][index]);S.extend([s,{v^1 for v in s}])
  Z=[[int(i!=j and not any(i in s and j in s for s in S)) for j in range(10)] for i in range(10)]
  target=tuple(root['q']+[Z[rho[i]][j]-Z[i][rho[j]] for i,j in pairs]);opts=[]
  for k in range(5):
   choices=[]
   for m in g['Q_domains'][2*k]:
    n=flip(m)
    if n not in g['Q_domains'][2*k+1]:continue
    Q=[{v for v in range(10) if mask&(1<<v)} for mask in [m,n]]
    C=[[sum(int(i in q and j in s) for q,s in zip(Q,S[2*k:2*k+2])) for j in range(10)] for i in range(10)]
    vec=tuple([sum(i in q for q in Q) for i in range(10)]+[C[i][j]-C[j][i] for i,j in pairs]);choices.append((m,vec))
   opts.append(choices)
  assert [len(x) for x in opts]==saved['domain_sizes'];np=math.prod(map(len,opts));assert np==saved['raw_products'];raw+=np
  # Different partition from the producer: paired rows 0,2 against 1,3,4.
  left={}
  for a,c in it.product(opts[0],opts[2]):
   vec=tuple(x+y for x,y in zip(a[1],c[1]));left.setdefault(vec,[]).append((a[0],c[0]))
  found=[]
  for bb,dd,ee in it.product(opts[1],opts[3],opts[4]):
   guard();need=tuple(t-x-y-z for t,x,y,z in zip(target,bb[1],dd[1],ee[1]))
   for aa,cc in left.get(need,[]):found.append((aa,bb[0],cc,dd[0],ee[0]))
  assert len(found)==len(set(found)) and set(found)==set(map(tuple,saved['survivors'])) and len(found)==len(saved['survivors']);solcount+=len(found)
  certs={r['assignment']:r for r in lm[key]['certificates']};assert not lm[key]['survivors'] and len(certs)==len(lm[key]['certificates']) and certs.keys()==set(range(len(saved['survivors'])))
  for ai,selected in enumerate(saved['survivors']):
   guard();rows=[{v for v in range(10) if mask&(1<<v)} for m in selected for mask in [m,flip(m)]]
   labels={(v,r) for v in range(10) for r in range(10) if r not in {rho[a] for a in S[v]}|rows[v]};assert len(labels)==50
   assert all(sum(e==r for v,e in labels)==8-sum(r in s for s in S) for r in range(10))
   demand=[[0]*10 for _ in range(10)]
   for v,r in labels:
    targets=set(range(10))-(S[v]|{rho[r]});assert len(targets)==6
    for e in targets:demand[r][e]+=1
   assert all(demand[i][j]==demand[j][i] for i,j in pairs)
   cert=certs[ai];assert cert['kind']=='odd_internal';r=cert['support'];assert cert['count']==demand[r][r] and demand[r][r]%2==1;negative+=1
 assert (raw,solcount,negative)==(72973467,59,59)
 status='COMPLETE'
except TimeoutError:pass
result={'status':status,'original_cap_seconds':30,'seconds':time.monotonic()-start,'hashes':nh,'raw_products':raw,'assignments':solcount,'odd_certificates':negative}
(o/'audit.json').write_text(json.dumps(result,indent=2)+'\n');print(result)
