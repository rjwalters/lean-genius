from pathlib import Path
import json,hashlib,itertools
ROOT=Path(__file__).resolve().parent;src=Path('/tmp/erdos85-sol1-q9-n78-kernel-eight-cayley-examples');pins={}
for n,h in json.loads((src/'pins.json').read_text()).items():
 f=src/n;assert hashlib.sha256(f.read_bytes()).hexdigest()==h;pins[str(f)]=h
r=json.loads((src/'results.json').read_text());out=[]
for group in r['groups']:
 G=group['group'];table=group['multiplication'];perms=[]
 for g in G:
  if group['name']=='dihedral_product':
   r0,f,c=g;perm=[(r0+(-1 if f else 1)*v)%4 for v in range(4)]+[4+(v+c)%3 for v in range(3)]
  else:
   x,n=g;perm=[]
   for v in range(8):
    bits=[(v>>i)&1 for i in range(3)];rotated=sum(bits[(i-n)%3]<<i for i in range(3));perm.append(x^rotated)
  perms.append(tuple(perm))
 assert len(set(perms))==24
 for a,b in itertools.product(range(24),repeat=2):assert perms[table[a][b]]==tuple(perms[a][perms[b][i]] for i in range(len(perms[a])))
 seen=set()
 for w in group['survivors']:
  S=tuple(w['S']);assert S not in seen;seen.add(S)
  assert len(S)==3 and sorted(G[s][-1] for s in S)==[0,1,2]
  adj=[set(row) for row in w['neighbors']];assert len(adj)==24
  for v in range(24):
   assert adj[v]=={table[v][s] for s in S}
   assert len(adj[v])==3 and v not in adj[v] and all(v in adj[u] for u in adj[v])
  assert all(len(adj[u]&adj[v])<=1 for u,v in itertools.combinations(range(24),2))
 out.append(dict(name=group['name'],multiplication_entries=576,positive_graphs=len(seen),codegree_checks=276*len(seen)))
assert [v['positive_graphs'] for v in out]==[16,48]
for w in json.loads((src/'witnesses.json').read_text()):
 group=next(g for g in r['groups'] if g['name']==w['name']);assert w['group']==group['group'] and w['multiplication']==group['multiplication'] and w['witness']==group['survivors'][0]
(ROOT/'input-pins.json').write_text(json.dumps(pins,indent=2)+'\n');(ROOT/'verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
