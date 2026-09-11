from pathlib import Path
import json,itertools as I,hashlib,sqlite3,time
p=Path(__file__).parent;src=Path('/Users/rwalters/lean-genius-q9-known-values-20260911/n78-two-four-cyclic-projection-exclusion');read=lambda f:json.loads(f.read_text());checks={}
for mf in [src/'pins.json',src/'input-pins.json']:
 for name,h in read(mf).items():
  f=mf.parent/name;assert hashlib.sha256(f.read_bytes()).hexdigest()==h;checks[str(f)]=h
con=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True);con.row_factory=sqlite3.Row
states=[dict(con.execute('select id,status,resolution from review_requests where id=?',(i,)).fetchone()) for i in [2257,2419,2425,2438,2441]];assert all(r['status']=='resolved' and r['resolution'].startswith('PASS') for r in states)
author=read(src/'results.json');assert author['status']=='COMPLETE';models={(r['alpha'],r['beta'],r['gamma']):r for r in author['models']};assert len(models)==len(author['models'])==8
els=list(I.product(range(2),range(4),range(2)));ix={x:i for i,x in enumerate(els)}
start=time.monotonic();records=[];status='INCOMPLETE'
try:
 for alpha,beta,gamma in I.product(range(2),repeat=3):
  if time.monotonic()-start>30:raise TimeoutError
  def multiply(x,y):
   i,j,e=els[x];k,l,f=els[y];word=[0]*i+[1]*j+[0]*k+[1]*l;central=e^f
   for end in range(len(word)-1,0,-1):
    for at in range(end):
     if word[at]>word[at+1]:central^=gamma;word[at],word[at+1]=word[at+1],word[at]
   na=word.count(0);nb=word.count(1);central^=(alpha*(na//2))^(beta*(nb//4))
   return ix[na%2,nb%4,central]
  M=[[multiply(x,y) for y in range(16)] for x in range(16)]
  assert all(M[M[x][y]][z]==M[x][M[y][z]] for x,y,z in I.product(range(16),repeat=3))
  orders=[]
  for x in range(16):
   power=0
   for n in range(1,17):
    power=M[power][x]
    if power==0:orders.append(n);break
   else:raise AssertionError('No finite order')
  saved=models[alpha,beta,gamma];assert M==saved['multiplication'] and orders==saved['orders'] and sum(o>2 for o in orders)==saved['noninvolutions']
  if gamma==1 and alpha==beta:
   t=ix[1,2,0];zin=ix[0,0,1];bin=ix[0,1,0]
   inv=[next(y for y in range(16) if M[x][y]==M[y][x]==0) for x in range(16)]
   assert {M[M[g][t]][inv[g]] for g in range(16)}=={t,ix[1,2,1]}
   assert orders[t]==2
   if alpha==0:assert sum(o>2 for o in orders)==8
   else:
    assert orders[bin]==8 and {M[x][x] for x,o in enumerate(orders) if o==8}=={ix[0,2,0],ix[0,2,1]}
    half=[x for x,e in enumerate(els) if e[1]==2];assert sorted(orders[x] for x in half)==[2,2,4,4]
    invol=[x for x,o in enumerate(orders) if o==2];assert len(invol)==3 and all(M[x][y]==M[y][x] for x,y in I.product(invol,repeat=2))
    b5=0
    for _ in range(5):b5=M[b5][bin]
    assert M[M[t][bin]][t]==b5
  records.append({'alpha':alpha,'beta':beta,'gamma':gamma,'orders':orders})
 # Every three distinct residues of C4 has a difference of two.
 assert all(any((a-b)%4==2 for a,b in I.combinations(s,2)) for s in I.combinations(range(4),3))
 status='COMPLETE'
except TimeoutError:pass
r={'status':status,'original_cap_seconds':30,'seconds':time.monotonic()-start,'hashes':checks,'premises':states,'records':records};(p/'results.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps({'status':status,'seconds':r['seconds'],'hashes':len(checks),'models':len(records)}))
