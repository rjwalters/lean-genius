from pathlib import Path
import json,itertools as it,hashlib,sqlite3,time,functools
p=Path('/tmp/erdos85-sol1-q9-n78-kernel-four-local-w');b=Path('/tmp/erdos85-sol1-q9-n78-kernel-four-partial-incidences');o=Path(__file__).parent
def read(f):return json.loads(f.read_text())
nh=0
for name in ['pins.json','input-pins.json']:
 for k,v in read(p/name).items():
  q=Path(k);q=q if q.is_absolute() else p/q
  assert hashlib.sha256(q.read_bytes()).hexdigest()==v;nh+=1
c=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True)
for rid in [2419,2451,2457,2461,2462,2474]:
 s,r=c.execute('select status,resolution from review_requests where id=?',(rid,)).fetchone();assert s=='resolved' and r.startswith('PASS')
base=read(b/'results.json');ext=read(b/'extension-results.json');att=read(b/'attachment-results.json');data=read(p/'results.json');assert all(x['status']=='COMPLETE' for x in [base,ext,att,data])
lookup={(r['attachment_source'],r['matching']):r for r in data['records']};positive=[i for i,a in enumerate(att['records']) if a['collision'] is None];assert len(lookup)==len(data['records'])==3456 and lookup.keys()==set(it.product(positive,[1,2,3]))
def mul(a,b):
 i,j=divmod(a,2);k,l=divmod(b,2);return 2*((i+pow(5,j)*k)%8)+(j^l)
start=time.monotonic();status='INCOMPLETE';ntest=npositive=localpositive=0
def guard():
 if time.monotonic()-start>30:raise TimeoutError
try:
 for ai in positive:
  guard();attachment=att['records'][ai];e=ext['records'][attachment['extension_source']];r=base['records'][e['source']];delta=attachment['delta'];N=[set() for _ in range(72)];centers={}
  def edge(a,b):N[a].add(b);N[b].add(a)
  for g in range(16):
   i,j=divmod(g,2);edge(8+g,8+mul(g,r['c']));edge(g//2,8+g);edge(g//2,mul(g,8)//2)
   for x in [mul(g,2*r['xp'])//2,8+g,8+mul(g,r['d'])]:edge(24+g,x)
   for x in r['D']:edge(40+g,8+mul(g,x))
   for x in [8+g]+[mul(g,2*t)//2 for t in e['pair']]:edge(56+g,x)
   centers[24+g]=j;centers[40+g]=2+((2*(i%2)+j)^delta);centers[56+g]=2+2*(i%2)+j
  supports={v:sum(1<<x for x in N[v]) for v in range(24,72)};assert all(m.bit_count()==3 for m in supports.values())
  for matching in [1,2,3]:
   rec=lookup[ai,matching];tests={t['origin']:t for t in rec['tests']};assert len(tests)==len(rec['tests'])==3 and tests.keys()=={24,40,56};flags=[]
   for w,t in tests.items():
    guard();covered={x for v in N[w] for x in N[v] if x<24};assert len(covered)==9
    target=sum(1<<x for x in range(24) if x not in covered);s=centers[w];mate=s^1 if s<2 else 2+((s-2)^matching)
    groups={k:[v for v in range(24,72) if v!=w and centers[v]==k and supports[v]&target==supports[v]] for k in range(6) if k!=mate}
    assert target==t['target'] and {int(k):v for k,v in t['groups'].items()}==groups
    options=[(v,supports[v],1<<k) for k,vs in groups.items() for v in vs];allcenters=sum(1<<k for k in groups)
    @functools.lru_cache(None)
    def solve(left,remaining):
     guard()
     if not left:return remaining==0
     eligible=[(v,m,k) for v,m,k in options if remaining&k and left&m==m]
     # Branch on a residual endpoint, unlike producer's fixed center order.
     choices=min(([x for x in eligible if x[1]&(1<<e)] for e in range(24) if left&(1<<e)),key=len)
     return any(solve(left^m,remaining^k) for v,m,k in choices)
    good=solve(target,allcenters);assert good==(t['witness'] is not None)
    if good:
     witness=t['witness'];assert len(witness)==len(set(witness))==5 and {centers[v] for v in witness}==set(groups)
     masks=[supports[v] for v in witness];assert sum(m.bit_count() for m in masks)==15 and sum(masks)==target and all(v in groups[centers[v]] for v in witness);localpositive+=1
    flags.append(good);ntest+=1
   assert rec['positive']==all(flags);npositive+=all(flags)
 assert ntest==10368 and npositive==0;status='COMPLETE'
except TimeoutError:pass
result={'status':status,'original_cap_seconds':30,'seconds':time.monotonic()-start,'hashes':nh,'local_tests':ntest,'local_positive':localpositive,'positive_cases':npositive};(o/'audit.json').write_text(json.dumps(result,indent=2)+'\n');print(result)
