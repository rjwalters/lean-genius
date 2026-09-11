import itertools
ps=list(itertools.permutations(range(3)));pairs=list(itertools.combinations(range(5),2));allwords=list(itertools.product(range(3),repeat=5))
def model(code):
 z=code;ds=[0]*10
 for i in range(9,-1,-1):ds[i]=z%6;z//=6
 P={}
 for (u,v),z in zip(pairs,ds):P[u,v]=ps[z];P[v,u]=tuple(ps[z].index(a) for a in range(3))
 U={(u,v,a,b):3-int(a!=0 and P[u,v][3-a]==b)-int(P[u,v][a]!=0 and 3-P[u,v][a]==b)-sum(P[t,v][P[u,t][a]]==b for t in range(5) if t not in (u,v)) for u,v in pairs for a in range(3) for b in range(3)}
 words=[];caps=[]
 for w in allwords:
  B=[[3-int(w[u]!=0 and a==3-w[u])-sum(P[v,u][w[v]]==a for v in range(5) if v!=u) for a in range(3)] for u in range(5)]
  if min(map(min,B))>=0 and all(U[u,v,w[u],w[v]]>0 for u,v in pairs):words.append(w);caps.append(B)
 n=len(words);edges=[]
 for i in range(n):
  for j in range(i,n):
   if i==j:
    if all(caps[i][u][words[i][u]]>=2 for u in range(5)):edges.append((i,j))
   elif sum(a==b for a,b in zip(words[i],words[j]))<=3 and all(caps[i][u][words[j][u]]>0 and caps[j][u][words[i][u]]>0 for u in range(5)):edges.append((i,j))
 A=[];rhs=[];labels=[]
 def add(row,b,label):A.append({k:v for k,v in row.items() if v});rhs.append(b);labels.append(label)
 for u in range(5):
  for a in range(3):
   for s in [-1,1]:add({i:s for i,w in enumerate(words) if w[u]==a},s*(4,3,3)[a],['margin',u,a,s])
 for u,v in pairs:
  for a in range(3):
   for b in range(3):add({i:1 for i,w in enumerate(words) if w[u]==a and w[v]==b},U[u,v,a,b],['pair',u,v,a,b])
 for i,w in enumerate(words):
  add({i:1},1,['selected_bound',i])
  incident=[(n+k,j if i==h else h) for k,(h,j) in enumerate(edges) if i in (h,j)]
  for s in [-1,1]:add({i:-4*s,**{k:s for k,j in incident}},0,['degree',i,s])
  for u in range(5):
   for a in range(3):add({i:-caps[i][u][a],**{k:1 for k,j in incident if words[j][u]==a}},0,['neighbor_margin',i,u,a])
  for k,j in incident:add({k:1,i:-2},0,['edge_bound',i,k])
 return {'code':code,'words':words,'edges':edges,'A':A,'rhs':rhs,'labels':labels,'variables':n+len(edges)}
