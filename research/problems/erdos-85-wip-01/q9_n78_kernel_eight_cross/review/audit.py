import json,hashlib,itertools
from pathlib import Path
ROOT=Path(__file__).resolve().parent;src=Path('/tmp/erdos85-sol1-q9-n78-kernel-eight-cross');pins={}
for n,h in json.loads((src/'pins.json').read_text()).items():
 f=src/n;assert hashlib.sha256(f.read_bytes()).hexdigest()==h;pins[str(f)]=h
for n,h in json.loads((src/'input-pins.json').read_text()).items():
 f=Path(n);assert hashlib.sha256(f.read_bytes()).hexdigest()==h;pins[str(f)]=h
base=Path('/tmp/erdos85-sol1-q9-n78-kernel-eight-cayley-examples/results.json');groups=json.loads(base.read_text())['groups'];out=[]
for w in json.loads((src/'witnesses.json').read_text()):
 group=next(g for g in groups if g['name']==w['name']);G=group['group'];mul=group['multiplication'];c=w['configuration']
 S=group['survivors'][c['left']]['S'];U=group['survivors'][c['right']]['S'];T=c['cross'];assert sorted(G[t][-1] for t in T)==[1,2]
 adj=[set() for _ in range(54)]
 def edge(a,b):adj[a].add(b);adj[b].add(a)
 for i in range(3):edge(i,i+3)
 for g in range(24):
  edge(6+g,G[g][-1]);edge(30+g,3+G[g][-1])
  for s in S:edge(6+g,6+mul[g][s])
  for u in U:edge(30+g,30+mul[g][u])
  for t in T:edge(6+g,30+mul[g][t])
 assert [sorted(a) for a in adj]==w['neighbors']
 assert [len(a) for a in adj]==[9]*6+[6]*48
 assert all(v not in adj[v] and all(v in adj[u] for u in adj[v]) for v in range(54))
 assert all(len(adj[a]&adj[b])<=1 for a,b in itertools.combinations(range(54),2))
 for h in range(24):
  perm=[(i+G[h][-1])%3 for i in range(3)]+[3+(i+G[h][-1])%3 for i in range(3)]+[6+mul[h][g] for g in range(24)]+[30+mul[h][g] for g in range(24)]
  assert sorted(perm)==list(range(54))
  assert all({perm[u] for u in adj[v]}==adj[perm[v]] for v in range(54))
 out.append(dict(name=w['name'],vertices=54,edges=sum(map(len,adj))//2,codegree_pairs=1431,group_actions_checked=24))
(ROOT/'input-pins.json').write_text(json.dumps(pins,indent=2)+'\n');(ROOT/'verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
