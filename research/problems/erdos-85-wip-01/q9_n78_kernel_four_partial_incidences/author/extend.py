from pathlib import Path
import json,itertools as I,time
p=Path(__file__).parent;prior=json.loads((p/'results.json').read_text());assert prior['status']=='COMPLETE'
els=list(map(tuple,prior['elements']));ix={x:i for i,x in enumerate(els)}
def mul(x,y):
 i,j=els[x];k,l=els[y];return ix[(i+(5 if j else 1)*k)%8,j^l]
M=[[mul(x,y) for y in range(16)] for x in range(16)];cosets=prior['cosets'];cx={g:i for i,C in enumerate(cosets) for g in C};r4=ix[4,0]
def edge(A,u,v):A[u].add(v);A[v].add(u)
def c4(A):
 seen={}
 for v,ns in enumerate(A):
  for a,b in I.combinations(sorted(ns),2):
   if (a,b) in seen:return [a,seen[a,b],b,v]
   seen[a,b]=v
 return None
start=time.monotonic();status='INCOMPLETE';out=[]
try:
 for ri,rec in enumerate(prior['records']):
  if rec['stage']!='W2' or rec['c4'] is not None:continue
  A=[set() for _ in range(56)];c,d,xp,D=(rec[k] for k in ['c','d','xp','D'])
  for g in range(16):
   edge(A,8+g,8+M[g][c]);edge(A,cx[g],8+g);edge(A,cx[g],cx[M[g][r4]])
   edge(A,24+g,cx[M[g][cosets[xp][0]]]);edge(A,24+g,8+g);edge(A,24+g,8+M[g][d])
   for h in D:edge(A,40+g,8+M[g][h])
  assert c4(A) is None
  for pair in I.combinations(range(8),2):
   if time.monotonic()-start>30:raise TimeoutError
   B=[set(x) for x in A]+[set() for _ in range(16)]
   for g in range(16):
    edge(B,56+g,8+g)
    for xp1 in pair:edge(B,56+g,cx[M[g][cosets[xp1][0]]])
   out.append({'source':ri,'pair':pair,'c4':c4(B)})
 status='COMPLETE'
except TimeoutError:pass
r={'status':status,'original_cap_seconds':30,'seconds':time.monotonic()-start,'records':out};(p/'extension-results.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({'status':status,'seconds':r['seconds'],'cases':len(out),'positive':sum(x['c4'] is None for x in out)}))
