import json,time,itertools,hashlib,sqlite3
from pathlib import Path
p=Path('/tmp/erdos85-sol1-q9-n78-kernel-four-extension-cover')
out=Path(__file__).parent
def read(f):return json.loads(f.read_text())
nh=0
for f in ['pins.json','input-pins.json']:
 for k,v in read(p/f).items():
  q=Path(k);q=q if q.is_absolute() else p/q
  assert hashlib.sha256(q.read_bytes()).hexdigest()==v;nh+=1
c=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True)
for rid in [2257,2451,2457]:
 s,r=c.execute('select status,resolution from review_requests where id=?',(rid,)).fetchone();assert s=='resolved' and r.startswith('PASS')
d=read(p/'results.json');ids=read(p/'identifications.json');assert d['status']==ids['status']=='COMPLETE'
start=time.monotonic();status='INCOMPLETE';counts={};retained=[]
def guard():
 if time.monotonic()-start>30:raise TimeoutError
try:
 for base in d['bases']:
  kind=base['kind']
  def mul(a,b):
   if kind=='C8':return (a+b)%8
   i,e=divmod(a,2);j,f=divmod(b,2)
   return 2*((i+(-1)**e*j)%4)+(e^f)
  def power(a,n):
   x=0
   for _ in range(n):x=mul(x,a)
   return x
  table=[[mul(a,b) for b in range(8)] for a in range(8)]
  assert table==base['multiplication']
  autos=set()
  if kind=='C8':
   for r in [1,3,5,7]:autos.add(tuple(power(r,i) for i in range(8)))
  else:
   for r,t in itertools.product(range(8),repeat=2):
    m=tuple(mul(power(r,i),power(t,e)) for i in range(4) for e in range(2))
    if len(set(m))==8 and all(m[mul(a,b)]==mul(m[a],m[b]) for a,b in itertools.product(range(8),repeat=2)):autos.add(m)
  assert autos==set(map(tuple,base['automorphisms']))
  rows=[(i,r) for i,r in enumerate(d['records']) if r['base']==kind]
  assert {(r['automorphism'],r['square']) for _,r in rows}==set(itertools.product(range(len(autos)),range(8))) and len(rows)==8*len(autos)
  for mi,rec in rows:
   guard();theta=base['automorphisms'][rec['automorphism']];square=rec['square']
   inv=next(a for a in range(8) if mul(square,a)==0)
   compatible=theta[square]==square and all(theta[theta[a]]==mul(mul(square,a),inv) for a in range(8))
   if not compatible:expected='INCOMPATIBLE_EXTENSION'
   else:
    def product(a,b):
     h,e=divmod(a,2);k,f=divmod(b,2)
     x=mul(h,theta[k] if e else k)
     return 2*(mul(x,square) if e*f else x)+(e^f)
    M=[[product(a,b) for b in range(16)] for a in range(16)]
    assert M==rec['multiplication']
    assert all(M[M[a][b]][v]==M[a][M[b][v]] for a,b,v in itertools.product(range(16),repeat=3))
    orders=[]
    for a in range(16):
     x=a;n=1
     while x: x=M[x][a];n+=1;assert n<=16
     orders.append(n)
    assert orders==rec['orders']
    n=[a for a in range(16) if orders[a]>2];nc=[a for a in range(16) if orders[a]==2 and any(M[a][b]!=M[b][a] for b in range(16))]
    assert n==rec['noninvolutions'] and nc==rec['noncentral_involutions']
    expected='INSUFFICIENT_FREE_PAIRS' if len(n)<10 else 'NO_NONCENTRAL_INVOLUTION' if not nc else 'RETAINED'
    if expected=='RETAINED':retained.append(mi)
   assert expected==rec['status'];counts[expected]=counts.get(expected,0)+1
 witnesses={r['model_record']:r for r in ids['records']};assert len(witnesses)==len(ids['records'])==10 and set(witnesses)==set(retained)
 for mi,w in witnesses.items():
  guard();M=d['records'][mi]['multiplication'];m=w['isomorphism'];k=w['exponent'];assert k in (3,5) and sorted(m)==list(range(16))
  for a,b in itertools.product(range(16),repeat=2):
   i,e=divmod(a,2);j,f=divmod(b,2)
   assert M[m[a]][m[b]]==m[2*((i+pow(k,e)*j)%8)+(e^f)]
 status='COMPLETE'
except TimeoutError:pass
result={'status':status,'original_cap_seconds':30,'seconds':time.monotonic()-start,'hashes':nh,'counts':counts,'retained':len(retained)}
(out/'audit.json').write_text(json.dumps(result,indent=2)+'\n');print(result)
