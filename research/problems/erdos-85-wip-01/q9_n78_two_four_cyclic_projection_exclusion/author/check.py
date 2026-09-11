from pathlib import Path
import itertools as I,json,time
p=Path(__file__).parent;start=time.monotonic();cap=30;els=list(I.product(range(2),range(4),range(2)));ix={x:i for i,x in enumerate(els)};out=[]
for alpha,beta,gamma in I.product((0,1),repeat=3):
 def mul(x,y):
  i,j,e=x;k,l,f=y
  return ((i+k)%2,(j+l)%4,(e+f+gamma*j*k+alpha*i*k+beta*((j+l)//4))%2)
 M=[[ix[mul(x,y)] for y in els] for x in els]
 for x,y,z in I.product(range(16),repeat=3):
  if time.monotonic()-start>cap:raise TimeoutError('Original30s extension audit cap')
  assert M[M[x][y]][z]==M[x][M[y][z]]
 inv=[next(j for j in range(16) if M[i][j]==M[j][i]==0) for i in range(16)]
 orders=[]
 for x in range(16):
  v=x;n=1
  while v: v=M[v][x];n+=1
  orders.append(n)
 a=ix[(1,0,0)];b=ix[(0,1,0)];z=ix[(0,0,1)];t=ix[(1,2,0)]
 assert M[a][a]==(z if alpha else 0) and M[M[b][b]][M[b][b]]==(z if beta else 0)
 if gamma==1 and alpha==beta:
  assert orders[t]==2
  cl=sorted({M[M[g][t]][inv[g]] for g in range(16)});assert cl==[t,ix[(1,2,1)]]
  noninv=sum(o>2 for o in orders);assert noninv==(8 if alpha==0 else 12)
  if alpha==1:
   half=[i for i,(u,v,e) in enumerate(els) if v==2];assert sorted(orders[i] for i in half)==[2,2,4,4]
   square={M[i][i] for i,o in enumerate(orders) if o==8};assert square=={ix[(0,2,0)],ix[(0,2,1)]}
 out.append({'alpha':alpha,'beta':beta,'gamma':gamma,'multiplication':M,'orders':orders,'noninvolutions':sum(o>2 for o in orders)})
r={'status':'COMPLETE','original_cap_seconds':cap,'seconds':time.monotonic()-start,'models':out};(p/'results.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({'status':r['status'],'seconds':r['seconds'],'counts':[(r['alpha'],r['beta'],r['gamma'],r['noninvolutions']) for r in out]}))
