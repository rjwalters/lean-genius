from pathlib import Path
import itertools,json,time
p=Path(__file__).parent;start=time.monotonic()
G=sorted(q for q in itertools.permutations(range(6)) if all(q[i^1]==(q[i]^1) for i in range(6)));assert len(G)==48
idx={g:i for i,g in enumerate(G)};identity=idx[tuple(range(6))]
mul=[[idx[tuple(a[b[k]] for k in range(6))] for b in G] for a in G]
inv=[next(j for j in range(48) if mul[i][j]==identity) for i in range(48)]
ones=[i for i in range(48) if i!=identity and inv[i]==i];pairs=[(i,inv[i]) for i in range(48) if i<inv[i]]
tested=targets=0;survive=[]
for np in range(3):
 for ps in itertools.combinations(pairs,np):
  for os in itertools.combinations(ones,5-2*np):
   if time.monotonic()-start>=60:raise RuntimeError('UNKNOWN original60s; no retry')
   S=sorted(list(os)+[i for pair in ps for i in pair]);tested+=1
   if [sum(G[i][0]==a for i in S) for a in range(6)]!=[1,0,1,1,1,1]:continue
   targets+=1;Sset=set(S)
   if any(len(Sset&{mul[g][s] for s in S})>(0 if G[g][0]==0 else 1) for g in range(48) if g!=identity):continue
   survive.append(S)
(p/'results.json').write_text(json.dumps({'status':'COMPLETE','original_seconds':60,'seconds':time.monotonic()-start,'group':G,'identity':identity,'involutions':len(ones),'inverse_pairs':len(pairs),'inverse_closed_sets':tested,'target_survivors':targets,'surviving_sets':survive},indent=2)+'\n')
print('COMPLETE',tested,targets,len(survive),time.monotonic()-start)
if survive:
 S=survive[0];adj=[set() for _ in range(54)]
 def edge(a,b):adj[a].add(b);adj[b].add(a)
 for i in (0,2,4):edge(i,i+1)
 for g in range(48):
  edge(6+g,G[g][0])
  for s in S:edge(6+g,6+mul[g][s])
 assert all(len(adj[i])==(9 if i<6 else 6) for i in range(54))
 assert all(len(adj[i]&adj[j])<=1 for i in range(54) for j in range(i))
 (p/'witness.json').write_text(json.dumps({'S':S,'neighbors':[sorted(a) for a in adj]},indent=2)+'\n')
