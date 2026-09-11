from pathlib import Path
import itertools as it,json,time
p=Path(__file__).parent;start=time.monotonic();cap=30
els=list(it.product(range(2),range(4),range(2)));ix={x:i for i,x in enumerate(els)}
def mul(a,b):
 z,r,s=a;w,t,u=b;return (z^w,(r+(-1 if s else 1)*t)%4,s^u)
M=[[ix[mul(a,b)] for b in els] for a in els];inv=[next(j for j in range(16) if M[i][j]==0) for i in range(16)]
connections=[D for D in it.combinations(range(1,16),2) if {inv[d] for d in D}==set(D)];records=[]
def add(N,a,b):N[a].add(b);N[b].add(a)
def good(N):return all(len(a&b)<=1 for a,b in it.combinations(N,2))
for refl in (0,1):
 K=[0,ix[(1,refl,1)]];cosets=sorted({tuple(sorted(M[a][h] for h in K)) for a in range(16)});labels={v:i for i,c in enumerate(cosets) for v in c};moves=[[labels[M[g][c[0]]] for c in cosets] for g in range(16)];matchings=[];seen=set()
 for a,b in it.combinations(range(8),2):
  if (a,b) in seen:continue
  O=sorted({tuple(sorted((moves[g][a],moves[g][b]))) for g in range(16)});seen.update(O);N=[set() for _ in range(8)]
  for x,y in O:add(N,x,y)
  if all(len(row)==1 for row in N):matchings.append(O)
 assert len(matchings)==3
 rec={'reflection':refl,'K':K,'cosets':cosets,'moves':moves,'matchings':matchings,'tested':0,'survivors':[]};records.append(rec)
 for mi,matching in enumerate(matchings):
  for di,D in enumerate(connections):
   for origin in range(8):
    assert time.monotonic()-start<cap;rec['tested']+=1;N=[set() for _ in range(24)]
    for a,b in matching:add(N,a,b)
    for g in range(16):
     add(N,8+g,moves[g][origin])
     for d in D:add(N,8+g,8+M[g][d])
    assert list(map(len,N))==[3]*24
    if good(N):rec['survivors'].append({'matching':mi,'connection':di,'origin':origin,'edges':[(a,b) for a in range(24) for b in sorted(N[a]) if a<b]})
r={'status':'COMPLETE','original_cap_seconds':cap,'seconds':time.monotonic()-start,'elements':els,'multiplication':M,'inverse':inv,'connections':connections,'records':records};(p/'results.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({'status':'COMPLETE','seconds':r['seconds'],'connections':len(connections),'counts':[(r['tested'],len(r['survivors'])) for r in records]}))
