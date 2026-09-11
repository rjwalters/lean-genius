from pathlib import Path
import itertools as it,json,time
p=Path(__file__).parent;start=time.monotonic();status='INCOMPLETE';records=[]
def guard():
 if time.monotonic()-start>30:raise TimeoutError
els=list(it.product(range(4),range(2),range(2)));index={x:i for i,x in enumerate(els)}
try:
 for a,b,c in it.product(range(2),repeat=3):
  guard()
  def mul(x,y):
   i,j,e=x;k,l,f=y;n=i+(-1)**j*k
   return (n%4,j^l,(e+f+c*j*k+b*j*l+a*(n//4))%2)
  M=[[index[mul(x,y)] for y in els] for x in els]
  assert all(M[0][x]==M[x][0]==x for x in range(16))
  assert all(M[M[x][y]][z]==M[x][M[y][z]] for x,y,z in it.product(range(16),repeat=3))
  inv=[next(y for y in range(16) if M[x][y]==M[y][x]==0) for x in range(16)]
  orders=[]
  for x in range(16):
   y=x;n=1
   while y:y=M[y][x];n+=1;assert n<=16
   orders.append(n)
  models=[]
  for u,v in [(0,1),(1,0),(1,1)]:
   guard();perms=[]
   for i,j,e in els:
    flip=(u*i+v*j)%2
    perms.append([x^flip for x in range(2)]+[2+(i+(-1)**j*x)%4 for x in range(4)])
   assert all(perms[M[x][y]]==[perms[x][perms[y][k]] for k in range(6)] for x,y in it.product(range(16),repeat=2))
   assert [x for x in range(16) if perms[x]==list(range(6))]==[0,1]
   remaining={x for x in range(16) if orders[x]==2 and perms[x][0]==1};classes=[]
   while remaining:
    x=min(remaining);cl=sorted({M[M[h][x]][inv[h]] for h in range(16)});assert set(cl)<=remaining;remaining-=set(cl)
    centralizer=sum(M[x][h]==M[h][x] for h in range(16));fixedS=sum(perms[x][k]==k for k in range(6));fixed8=centralizer//2
    classes.append({'representative':x,'elements':cl,'fixed_S':fixedS,'fixed_on_own_eight_orbit':fixed8,'admissible_by_six_fixed':fixedS+fixed8<=6})
   models.append({'character':[u,v],'S_action':perms,'outside_stabilizer_classes':classes})
  records.append({'bits':[a,b,c],'multiplication':M,'orders':orders,'models':models})
 status='COMPLETE'
except TimeoutError:pass
result={'status':status,'original_cap_seconds':30,'seconds':time.monotonic()-start,'element_labels':els,'records':records}
(p/'results.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'status':status,'seconds':result['seconds'],'laws':len(records),'models':sum(len(r['models']) for r in records)}))
