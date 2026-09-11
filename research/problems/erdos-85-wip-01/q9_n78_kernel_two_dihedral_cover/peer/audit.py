from pathlib import Path
import json,hashlib,sqlite3,itertools as I,time
p=Path(__file__).parent;src=Path('/Users/rwalters/lean-genius-q9-known-values-20260911/n78-kernel-two-dihedral-cover');read=lambda f:json.loads(f.read_text());hashes={}
for manifest in ['pins.json','input-pins.json']:
 for name,h in read(src/manifest).items():
  f=src/name;assert hashlib.sha256(f.read_bytes()).hexdigest()==h;hashes[str(f)]=h
con=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True);con.row_factory=sqlite3.Row
states=[dict(con.execute('select id,status,resolution from review_requests where id=?',(i,)).fetchone()) for i in [2257,2419,2450]];assert all(x['status']=='resolved' and x['resolution'].startswith('PASS') for x in states)
data=read(src/'results.json');assert data['status']=='COMPLETE';els=list(I.product(range(4),range(2),range(2)));ix={e:i for i,e in enumerate(els)};assert list(map(tuple,data['element_labels']))==els
assert [tuple(r['bits']) for r in data['records']]==list(I.product(range(2),repeat=3))
start=time.monotonic();out=[];status='INCOMPLETE'
try:
 for record in data['records']:
  assert time.monotonic()-start<30
  a,b,c=record['bits']
  def word(x,y):
   i,j,e=x
   for gen in ['r']*y[0]+['s']*y[1]+['z']*y[2]:
    if gen=='z':e^=1
    elif gen=='s':
     if j:e^=b
     j^=1
    else:
     if j:i-=1;e^=c
     else:i+=1
     if i<0:i+=4;e^=a
     if i>=4:i-=4;e^=a
   return ix[i,j,e]
  M=[[word(x,y) for y in els] for x in els];assert M==record['multiplication']
  assert all(M[0][x]==M[x][0]==x for x in range(16))
  assert all(M[M[x][y]][z]==M[x][M[y][z]] for x,y,z in I.product(range(16),repeat=3))
  orders=[]
  for x in range(16):
   v=0
   for n in range(1,17):
    v=M[v][x]
    if v==0:orders.append(n);break
  assert orders==record['orders']
  assert [m['character'] for m in record['models']]==[[0,1],[1,0],[1,1]]
  for model in record['models']:
   u,v=model['character'];rperm=[u,1^u,3,4,5,2];sperm=[v,1^v,2,5,4,3]
   action=[]
   for i,j,e in els:
    perm=list(range(6))
    for gen in [sperm]*j+[rperm]*i:perm=[gen[t] for t in perm]
    action.append(perm)
   assert action==model['S_action'];assert [i for i,x in enumerate(action) if x==list(range(6))]==[0,1]
   assert all(action[M[x][y]]==[action[x][action[y][t]] for t in range(6)] for x,y in I.product(range(16),repeat=2))
   eligible={x for x in range(16) if orders[x]==2 and action[x][0]==1};classes=[]
   while eligible:
    t=min(eligible);cosets={frozenset([g,M[g][t]]) for g in range(16)};assert len(cosets)==8
    fixed={x:sum(frozenset(M[x][g] for g in C)==C for C in cosets) for x in range(1,16)}
    cl=sorted(x for x,n in fixed.items() if n);assert set(cl)<=eligible;eligible-=set(cl)
    sf=sum(a==b for a,b in enumerate(action[t]));f8=fixed[t]
    classes.append({'representative':t,'elements':cl,'fixed_S':sf,'fixed_on_own_eight_orbit':f8,'admissible_by_six_fixed':sf+f8<=6})
   assert classes==model['outside_stabilizer_classes']
   out.append({'bits':record['bits'],'character':[u,v],'classes':classes})
 status='COMPLETE'
except TimeoutError:pass
result={'status':status,'original_cap_seconds':30,'seconds':time.monotonic()-start,'hashes':hashes,'premises':states,'records':out};(p/'results.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'status':status,'seconds':result['seconds'],'hashes':len(hashes),'actions':len(out)}))
