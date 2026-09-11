from pathlib import Path
import json,itertools as it,hashlib,sqlite3,time
p=Path('/tmp/erdos85-sol1-q9-n78-kernel-four-partial-incidences');o=Path(__file__).parent
def read(f):return json.loads(f.read_text())
nh=0
for name in ['pins.json','input-pins.json']:
 for k,v in read(p/name).items():
  q=Path(k);q=q if q.is_absolute() else p/q
  assert hashlib.sha256(q.read_bytes()).hexdigest()==v;nh+=1
c=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True)
for rid in [2451,2457,2461,2462]:
 s,r=c.execute('select status,resolution from review_requests where id=?',(rid,)).fetchone();assert s=='resolved' and r.startswith('PASS')
d=read(p/'results.json');ex=read(p/'extension-results.json');at=read(p/'attachment-results.json');assert d['status']==ex['status']==at['status']=='COMPLETE'
def mul(a,b):
 i,j=divmod(a,2);k,l=divmod(b,2);return 2*((i+pow(5,j)*k)%8)+(j^l)
inv=[next(b for b in range(16) if mul(a,b)==0) for a in range(16)]
connections=[a for a in range(16) if (a//2)%2 and a<inv[a]]
triples=[(0,a,b) for a,b in it.combinations(range(1,16),2) if len({0,2*((a//2)%2)+a%2,2*((b//2)%2)+b%2})==3]
assert connections==d['connections'] and list(range(1,16,2))==d['W0_pairs'] and triples==list(map(tuple,d['W2_triples']))
assert d['cosets']==[[2*i,2*i+1] for i in range(8)]
def build(c,d=None,xp=None,D=None,pair=None):
 n=24 if d is None else 40 if D is None else 56 if pair is None else 72
 N=[0]*n
 def edge(a,b):assert a!=b;N[a]|=1<<b;N[b]|=1<<a
 for g in range(16):
  edge(8+g,8+mul(g,c));edge(g//2,8+g);edge(g//2,mul(g,8)//2)
  if d is not None:
   edge(24+g,mul(g,2*xp)//2);edge(24+g,8+g);edge(24+g,8+mul(g,d))
  if D is not None:
   for h in D:edge(40+g,8+mul(g,h))
  if pair is not None:
   edge(56+g,8+g)
   for x in pair:edge(56+g,mul(g,2*x)//2)
 return N
def clean(N):return all((N[i]&N[j]).bit_count()<=1 for i,j in it.combinations(range(len(N)),2))
def cert(N,C):assert len(set(C))==4 and all(N[C[i]]&(1<<C[(i+1)%4]) for i in range(4))
stage={};start=time.monotonic();status='INCOMPLETE'
def guard():
 if time.monotonic()-start>30:raise TimeoutError
try:
 lookup={}
 for i,r in enumerate(d['records']):
  key=(r['c'],r.get('d'),r.get('xp'),tuple(r['D']) if 'D' in r else None)
  assert key not in lookup;lookup[key]=(i,r)
 visited=set();positive=[]
 for cc in connections:
  assert clean(build(cc))
  for dd,x in it.product(range(1,16,2),range(8)):
   guard();N=build(cc,dd,x)
   if not clean(N):
    key=(cc,dd,x,None);i,r=lookup[key];assert r['stage']=='W0';cert(N,r['c4']);visited.add(key);continue
   for D in triples:
    key=(cc,dd,x,D);i,r=lookup[key];assert r['stage']=='W2';visited.add(key);B=build(cc,dd,x,D)
    if r['c4'] is None:assert clean(B);positive.append(i)
    else:cert(B,r['c4'])
 assert visited==lookup.keys() and len(positive)==576
 status='COMPLETE'
except TimeoutError:pass
stage['first']={'status':status,'seconds':time.monotonic()-start,'positives':len(positive)}
(o/'stage1.json').write_text(json.dumps(stage['first'])+'\n')
assert status=='COMPLETE'
start=time.monotonic();status='INCOMPLETE';survivors=[]
try:
 lookup={(r['source'],tuple(r['pair'])):(i,r) for i,r in enumerate(ex['records'])};assert len(lookup)==len(ex['records'])
 expected={(i,pair) for i in positive for pair in it.combinations(range(8),2)};assert lookup.keys()==expected and len(expected)==16128
 for key,(ei,r) in lookup.items():
  guard();s=d['records'][key[0]];N=build(s['c'],s['d'],s['xp'],s['D'],key[1])
  if r['c4'] is None:assert clean(N);survivors.append(ei)
  else:cert(N,r['c4'])
 assert len(survivors)==1152;status='COMPLETE'
except TimeoutError:pass
stage['second']={'status':status,'seconds':time.monotonic()-start,'positives':len(survivors)}
(o/'stage2.json').write_text(json.dumps(stage['second'])+'\n');assert status=='COMPLETE'
start=time.monotonic();status='INCOMPLETE';npositive=0
try:
 lookup={(r['extension_source'],r['delta']):r for r in at['records']};assert len(lookup)==len(at['records'])==4608 and lookup.keys()==set(it.product(survivors,range(4)))
 for ei in survivors:
  guard();e=ex['records'][ei];s=d['records'][e['source']];N=build(s['c'],s['d'],s['xp'],s['D'],e['pair'])
  for delta in range(4):
   def center(w):
    g=(w-24)%16;i,j=divmod(g,2)
    return j if w<40 else 2+((2*(i%2)+j)^(delta if w<56 else 0))
   good=True
   for r in range(24):
    W=[w for w in range(24,72) if N[r]&(1<<w)];assert len(W)==6
    if len({center(w) for w in W})<6:good=False
   record=lookup[ei,delta];assert good==(record['collision'] is None)
   if good:npositive+=1
   else:
    z=record['collision'];ws=[(24 if kind==0 else 56 if kind==1 else 40)+g for kind,g in z['W']]
    assert ws[0]!=ws[1] and all(N[z['residual']]&(1<<w) for w in ws) and center(ws[0])==center(ws[1])==z['center']
 assert npositive==1152;status='COMPLETE'
except TimeoutError:pass
stage['third']={'status':status,'seconds':time.monotonic()-start,'positives':npositive}
(o/'stage3.json').write_text(json.dumps(stage['third'])+'\n');(o/'audit.json').write_text(json.dumps({'hashes':nh,'original_caps_seconds':[30,30,30],'stages':stage},indent=2)+'\n');print(stage)
