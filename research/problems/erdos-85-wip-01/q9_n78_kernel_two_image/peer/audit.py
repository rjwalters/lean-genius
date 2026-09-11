from pathlib import Path
import itertools,json
root=Path(__file__).parent;identity=tuple(range(6));parts={k:[] for k in ['cyclic_edge','even_flips','rotational']}
for sigma in itertools.permutations(range(3)):
 sign=sum(sigma[i]>sigma[j] for i in range(3) for j in range(i+1,3))%2
 for v in itertools.product(range(2),repeat=3):
  perm=tuple(2*sigma[i]+(b^v[sigma[i]]) for i in range(3) for b in range(2));parity=sum(v)%2
  for name,include in [('cyclic_edge',sign==0),('even_flips',parity==0),('rotational',parity==sign)]:
   if include:parts[name].append(perm)
summary={}
for name,G in parts.items():
 assert len(set(G))==24
 assert all(tuple(a[b[i]] for i in range(6)) in G for a in G for b in G)
 invol=[g for g in G if g!=identity and all(g[g[i]]==i for i in range(6))]
 free=[g for g in invol if all(g[i]!=i for i in range(6))]
 summary[name]={'size':24,'involutions':len(invol),'fixed_free_involutions':len(free)}
 if name=='cyclic_edge':assert free==[tuple(i^1 for i in range(6))]
 if name=='even_flips':assert not free
 if name=='rotational':
  orders=[]
  for f in range(6):
   H=[g for g in G if g[f]==f];assert len(H)==4
   assert any(tuple(g[g[i]] for i in range(6))!=identity for g in H)
   orders.append(4)
  summary[name]['cyclic_stabilizer_orders']=orders
(root/'results.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary))
