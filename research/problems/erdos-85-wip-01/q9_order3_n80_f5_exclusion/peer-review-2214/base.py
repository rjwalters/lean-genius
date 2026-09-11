from itertools import permutations,combinations,product
ps=list(permutations(range(3)));pairs=list(combinations(range(5),2));E=[[0,0,0],[0,0,1],[0,1,0]]
def mul(A,B):return [[sum(A[a][t]*B[t][b] for t in range(3)) for b in range(3)] for a in range(3)]
def independent(code):
 digits=[];z=code
 for i in range(10):digits.append(z%6);z//=6
 assert z==0;digits.reverse();M={}
 for (u,v),k in zip(pairs,digits):
  M[u,v]=[[int(ps[k][a]==b) for b in range(3)] for a in range(3)];M[v,u]=list(map(list,zip(*M[u,v])))
 U={}
 for u,v in pairs:
  summands=[mul(E,M[u,v]),mul(M[u,v],E)]+[mul(M[u,t],M[t,v]) for t in range(5) if t not in (u,v)]
  U[u,v]=[[3-sum(A[a][b] for A in summands) for b in range(3)] for a in range(3)]
 words=[];bounds=[]
 for w in product(range(3),repeat=5):
  b=[[3-E[w[u]][a]-sum(M[v,u][w[v]][a] for v in range(5) if v!=u) for a in range(3)] for u in range(5)]
  if any(x<0 for row in b for x in row) or any(U[u,v][w[u]][w[v]]<=0 for u,v in pairs):continue
  words.append(w);bounds.append(b)
 n=len(words);edges=[]
 for i,w in enumerate(words):
  for j in range(i,n):
   z=words[j]
   if i==j:
    allowed=min(bounds[i][u][w[u]] for u in range(5))>=2
   else:
    allowed=sum(a==b for a,b in zip(w,z))<=3 and all(bounds[i][u][z[u]]>=1 and bounds[j][u][w[u]]>=1 for u in range(5))
   if allowed:edges.append((i,j))
 rows=[];rhs=[];labels=[]
 def add(row,b,label):rows.append({k:v for k,v in row.items() if v});rhs.append(b);labels.append(label)
 for u in range(5):
  for a in range(3):
   for sign in (-1,1):add({i:sign for i,w in enumerate(words) if w[u]==a},sign*(4,3,3)[a],['margin',u,a,sign])
 for u,v in pairs:
  for a in range(3):
   for b in range(3):add({i:1 for i,w in enumerate(words) if (w[u],w[v])==(a,b)},U[u,v][a][b],['pair',u,v,a,b])
 for i,w in enumerate(words):
  add({i:1},1,['selected_bound',i]);inc={}
  for k,(a,b) in enumerate(edges):
   if a==i:inc[n+k]=b
   elif b==i:inc[n+k]=a
  for sign in (-1,1):
   row={i:-4*sign};row.update({k:sign for k in inc});add(row,0,['degree',i,sign])
  for u in range(5):
   for a in range(3):
    row={i:-bounds[i][u][a]};row.update({k:1 for k,j in inc.items() if words[j][u]==a});add(row,0,['neighbor_margin',i,u,a])
  for k in inc:add({i:-2,k:1},0,['edge_bound',i,k])
 return {'code':code,'words':words,'edges':edges,'A':rows,'rhs':rhs,'labels':labels,'variables':n+len(edges)}
