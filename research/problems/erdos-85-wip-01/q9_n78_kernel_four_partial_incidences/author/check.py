from pathlib import Path
import itertools as I,json,time
p=Path(__file__).parent
els=list(I.product(range(8),range(2)));ix={x:i for i,x in enumerate(els)}
def mul(x,y):
 i,j=els[x];k,l=els[y];return ix[(i+(5 if j else 1)*k)%8,j^l]
M=[[mul(x,y) for y in range(16)] for x in range(16)]
inv=[next(y for y in range(16) if M[x][y]==M[y][x]==0) for x in range(16)]
t=ix[0,1];r4=ix[4,0]
cosets=sorted({tuple(sorted((g,M[g][t]))) for g in range(16)});cx={g:i for i,C in enumerate(cosets) for g in C}
def residue(g):i,j=els[g];return i%2,j
connections=[g for g in range(1,16) if els[g][0]%2 and g<inv[g]]
pairs=[d for d in range(16) if els[d][1]==1]
triples=[(0,a,b) for a,b in I.combinations(range(1,16),2) if len({residue(0),residue(a),residue(b)})==3]
def edge(adj,u,v):adj[u].add(v);adj[v].add(u)
def c4(adj):
 seen={}
 for v,ns in enumerate(adj):
  for a,b in I.combinations(sorted(ns),2):
   if (a,b) in seen:return [a,seen[a,b],b,v]
   seen[a,b]=v
 return None
start=time.monotonic();status='INCOMPLETE';records=[];counts={'base':0,'W0':0,'W2':0,'positive':0}
try:
 for c in connections:
  base=[set() for _ in range(24)]
  for g in range(16):
   edge(base,8+g,8+M[g][c]);edge(base,cx[g],8+g);edge(base,cx[g],cx[M[g][r4]])
  bad=c4(base);counts['base']+=1
  if bad:records.append({'c':c,'stage':'base','c4':bad});continue
  for d in pairs:
   for xp in range(8):
    if time.monotonic()-start>30:raise TimeoutError
    A=[set(x) for x in base]+[set() for _ in range(16)]
    for g in range(16):
     edge(A,24+g,cx[M[g][cosets[xp][0]]]);edge(A,24+g,8+g);edge(A,24+g,8+M[g][d])
    bad=c4(A);counts['W0']+=1
    if bad:records.append({'c':c,'d':d,'xp':xp,'stage':'W0','c4':bad});continue
    for D in triples:
     if time.monotonic()-start>30:raise TimeoutError
     B=[set(x) for x in A]+[set() for _ in range(16)]
     for g in range(16):
      for h in D:edge(B,40+g,8+M[g][h])
     bad=c4(B);counts['W2']+=1;counts['positive']+=bad is None
     records.append({'c':c,'d':d,'xp':xp,'D':D,'stage':'W2','c4':bad})
 status='COMPLETE'
except TimeoutError:pass
out={'status':status,'original_cap_seconds':30,'seconds':time.monotonic()-start,'elements':els,'cosets':cosets,'connections':connections,'W0_pairs':pairs,'W2_triples':triples,'counts':counts,'records':records};(p/'results.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:out[k] for k in ['status','seconds','counts']}))
