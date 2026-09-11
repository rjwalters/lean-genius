from pathlib import Path
import json,itertools as I,hashlib,sqlite3,time
p=Path(__file__).parent;src=Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3/residual-ten-D5-five-311-packing');read=lambda f:json.loads(f.read_text());checks={}
for mf in [src/'pins.json',src/'input-pins.json']:
 for name,h in read(mf).items():
  f=mf.parent/name;assert hashlib.sha256(f.read_bytes()).hexdigest()==h;checks[str(f)]=h
c=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True);c.row_factory=sqlite3.Row
states=[dict(c.execute('select id,status,resolution from review_requests where id=?',(i,)).fetchone()) for i in [2251,2458,2460]];assert all(r['status']=='resolved' and r['resolution'].startswith('PASS') for r in states)
classes=read(src.parent/'residual-ten-D5-supports/results.json')['records'];saved=read(src/'results.json');assert saved['status']=='COMPLETE';assert [r['class'] for r in saved['records']]==list(range(8))
start=time.monotonic();out=[];status='INCOMPLETE';pairs=set(I.combinations(range(10),2))
def guard():
 if time.monotonic()-start>30:raise TimeoutError
try:
 for ci,cl in enumerate(classes):
  R=[set() for _ in range(10)]
  for a,b in cl['edges']:R[a].add(b);R[b].add(a)
  occupied={edge for s in R for edge in I.combinations(sorted(s),2)}
  supports=[(set(s),{x^1 for x in s}) for s in cl['high3']]
  used=[{edge for s in ss for edge in I.combinations(sorted(s),2)} for ss in supports]
  assert all(len(u)==6 and not u&occupied for u in used)
  counts=[0,0,0];positives=[]
  def extend(at,chosen,taken):
   guard()
   if len(chosen)==5:
    counts[0]+=1;S=[s for j in chosen for s in supports[j]]
    low=[9-len(R[e])-sum(e in s for s in S) for e in range(10)]
    if min(low)<0:return
    Z=[set() for _ in range(10)]
    for a,b in pairs-taken:Z[a].add(b);Z[b].add(a)
    q=[6-len(R[e])-len(Z[e]) for e in range(10)]
    if min(q)<0:return
    counts[1]+=1
    for a,b in pairs:
     d=len(R[a]&Z[b])-len(Z[a]&R[b])
     if not -q[b]<=d<=q[a]:return
    counts[2]+=1;positives.append({'high3':chosen,'q':q});return
   for j in range(at,len(supports)-(5-len(chosen))+1):
    if not used[j]&taken:extend(j+1,chosen+[j],taken|used[j])
  extend(0,[],occupied)
  claim=saved['records'][ci];assert claim['status']=='COMPLETE'
  assert counts==[claim[k] for k in ['compatible_packings','q_nonnegative','comm_pass']] and positives==claim['survivors']
  out.append({'class':ci,'counts':counts})
 status='COMPLETE'
except TimeoutError:pass
r={'status':status,'original_cap_seconds':30,'seconds':time.monotonic()-start,'hashes':checks,'premises':states,'records':out};(p/'results.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({'status':status,'seconds':r['seconds'],'hashes':len(checks),'records':out}))
