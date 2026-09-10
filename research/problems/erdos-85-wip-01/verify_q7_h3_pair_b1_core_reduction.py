"""Regenerate normalized H3 pair cores with P0 adjacent to P1."""
from itertools import combinations, permutations, product
from pathlib import Path
import json

def generate():
 colors=[[4,5,8,9,10,11],[3,6,12,13,14,15],[7,16,17,18,19,20]]
 matchings=[[(0,j),tuple(x for x in range(1,4) if x!=j)] for j in range(1,4)]
 groups=[]
 for same in [True,False]:
  m0,m1=1,2 if same else 3
  for eps in [0,1]:
   base=[(0,1),(0,3),(1,4),(2,5),(2,6),(2,7),(5,16+m0),(6,16+m1),(7,16),(17,18),(19,20)]
   for i in range(3):base.extend((21+i,v) for v in [a for a in range(3) if a!=i]+colors[i])
   for i,m in [(0,m0),(1,m1)]:base.extend((8+4*i+j,16+v) for j,v in enumerate(x for x in range(5) if x!=m))
   accepted=[];checked=0
   for M0,M1 in product(matchings,repeat=2):
    fixed=base+[(8+u,8+v) for u,v in M0]+[(12+u,12+v) for u,v in M1]
    cross=[]
    if eps:
     for ps in permutations(range(4)):cross.append([(3,4)]+[(8+u,12+v) for u,v in enumerate(ps)])
    else:
     for a,b in product(range(4),repeat=2):
      for ps in permutations([v for v in range(4) if v!=b]):cross.append([(3,8+a),(4,12+b)]+[(8+u,12+v) for u,v in zip([u for u in range(4) if u!=a],ps)])
    for ce in cross:
     checked+=1;edges=fixed+ce;adj=[set() for _ in range(24)]
     assert len(edges)==52 and len({tuple(sorted(e)) for e in edges})==52
     for u,v in edges:adj[u].add(v);adj[v].add(u)
     if any(len(adj[u]&adj[v])>1 for u,v in combinations(range(24),2)):continue
     assert [len(x) for x in adj]==[4,4,5]+[3]*5+[4]*13+[8]*3
     hosts=[[s for s in colors[i] if not(adj[i]&adj[s])] for i in range(3)]
     assert list(map(len,hosts))==[4,4,3]
     triples=[t for t in product(*colors) if all(not(adj[u]&adj[v]) for u,v in combinations(t,2))]
     accepted.append({'edges':edges,'colors':colors,'hosts':hosts,'triples':triples})
   assert checked==(216 if eps else 864)
   assert len(accepted)==(0 if eps else (36 if same else 39))
   groups.append({'same_edge':same,'epsilon':eps,'checked':checked,'accepted':accepted})
 return groups

if __name__=='__main__':
 groups=generate()
 Path(__file__).with_name('q7_h3_pair_b1_core_reduction.json').write_text(json.dumps(groups,indent=2)+'\n')
 print('Regenerated',sum(g['checked'] for g in groups),'choices;',sum(len(g['accepted']) for g in groups),'cores')
