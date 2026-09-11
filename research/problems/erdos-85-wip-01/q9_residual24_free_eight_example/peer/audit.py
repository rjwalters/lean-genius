from pathlib import Path
import json,hashlib,itertools
p=Path(__file__).parent;src=Path('/Users/rwalters/lean-genius-q9-known-values-20260911/residual24-free-eight-example')
pins=json.loads((src/'pins.json').read_text())
for f,h in pins.items():assert hashlib.sha256((src/f).read_bytes()).hexdigest()==h
w=json.loads((src/'witness.json').read_text());G=list(map(set,w['neighbors']));a=w['automorphism']
assert len(G)==24 and sorted(a)==list(range(24))
assert all(len(row)==3 and len(w['neighbors'][v])==3 and v not in row and all(0<=u<24 and v in G[u] for u in row) for v,row in enumerate(G))
codegrees=[len(G[i]&G[j]) for i,j in itertools.combinations(range(24),2)];assert max(codegrees)==1
assert all({a[x] for x in G[v]}==G[a[v]] for v in range(24))
for v in range(24):
 orbit=[];x=v
 while x not in orbit:orbit.append(x);x=a[x]
 assert x==v and len(orbit)==8
expected=[set() for _ in range(24)]
def edge(x,y):expected[x].add(y);expected[y].add(x)
for g in range(8):
 edge(g,(g+4)%8);edge(g,8+g);edge(g,16+g)
 for d in (1,2):edge(8+g,16+(g+d)%8)
assert expected==G
(p/'results.json').write_text(json.dumps({'source_pins':pins,'vertices':24,'edges':36,'degree':3,'codegree_pairs_checked':276,'max_codegree':1,'automorphism_orbits':[8,8,8],'construction_matches':True},indent=2)+'\n')
print('PASS: explicit cubic24 C4-free graph, all276 codegrees, free order8 automorphism')
