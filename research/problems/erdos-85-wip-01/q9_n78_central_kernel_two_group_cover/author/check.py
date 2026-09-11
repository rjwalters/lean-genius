from pathlib import Path
import itertools as I,json,time
p=Path(__file__).parent;start=time.monotonic();cap=30;models=[];cross=[(1,0),(2,0),(2,1)];choices=0
for a in I.product((0,1),repeat=3):
 for b in I.product((0,1),repeat=3):
  choices+=1
  if (sum(a)+sum(b))%2 or len(set(b))==1:continue
  def f(v,w):return (sum(a[i]*((v>>i)&1)*((w>>i)&1) for i in range(3))+sum(c*((v>>i)&1)*((w>>j)&1) for c,(i,j) in zip(b,cross)))%2
  M=[[2*((x//2)^(y//2))+((x%2)^(y%2)^f(x//2,y//2)) for y in range(16)] for x in range(16)]
  for x in range(16):
   if time.monotonic()-start>cap:raise TimeoutError('Original30s group audit cap')
   for y in range(16):
    for z in range(16):assert M[M[x][y]][z]==M[x][M[y][z]]
  assert M[0]==list(range(16)) and all(M[x][0]==x for x in range(16))
  inv=[next(y for y in range(16) if M[x][y]==M[y][x]==0) for x in range(16)]
  assert all(M[x][1]==M[1][x] for x in range(16)) and M[1][1]==0
  assert all(M[x][y]//2==(x//2)^(y//2) for x in range(16) for y in range(16))
  t=14;assert M[t][t]==0
  conj=sorted({M[M[g][t]][inv[g]] for g in range(16)});assert conj==[14,15]
  assert sum(M[g][t]==M[t][g] for g in range(16))==8
  cosets=sorted({tuple(sorted((g,M[g][t]))) for g in range(16)});labels={g:i for i,c in enumerate(cosets) for g in c}
  moves=[[labels[M[g][c[0]]] for c in cosets] for g in range(16)]
  S=[[2*i+(c^((g//2>>i)&1)) for i in range(3) for c in range(2)] for g in range(16)]
  assert [g for g in range(16) if S[g]==list(range(6))]==[0,1]
  assert sum(moves[t][i]==i for i in range(8))==4
  models.append({'square_bits':a,'commutator_bits':b,'multiplication':M,'inverse':inv,'S_action':S,'stabilizer':[0,t],'cosets':cosets,'X_action':moves})
assert choices==64 and len(models)==24
r={'status':'COMPLETE','original_cap_seconds':cap,'seconds':time.monotonic()-start,'parameter_choices':choices,'models':models};(p/'results.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({k:(len(v) if k=='models' else v) for k,v in r.items()}))
