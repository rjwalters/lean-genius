import time
from families import reconstruct

def verify(graph,cert,deadline):
 g=[set(v for v in range(49) if mask>>v&1) for mask in graph]
 status=cert['status'];nodes=branches=0
 families,capacity=reconstruct(graph,cert['pair_vertex'] if status=='EMPTY_FAMILY' else None)
 if status=='EMPTY_FAMILY':
  assert not families[cert['pair_vertex']]
  return 0,0
 assert status in ['INFEASIBLE_PROJECTION','FEASIBLE_PROJECTION']
 saved={int(u):[frozenset(s+7 for s in range(14) if mask>>s&1) for mask in masks] for u,masks in cert['families'].items()}
 assert set(saved)==set(families)
 assert all(len(saved[u])==len(set(saved[u])) and set(saved[u])==set(families[u]) for u in families)
 assert cert['capacity']==[capacity[s] for s in range(7,21)]
 if status=='FEASIBLE_PROJECTION':
  chosen={int(u):frozenset(s+7 for s in range(14) if mask>>s&1) for u,mask in cert['witness'].items()}
  assert set(chosen)==set(families) and all(chosen[u] in families[u] for u in families)
  assert all(sum(s in f for f in chosen.values())==capacity[s] for s in capacity)
  assert all(len(chosen[u]&chosen[v])+len(g[u]&g[v])<=1 for u in chosen for v in chosen if u<v)
  return 0,0
 order=cert['order'];assert len(order)==21 and set(order)==set(saved)
 tree=cert['tree'];seen=set()
 def visit(index,depth,chosen,usage):
  nonlocal nodes,branches
  assert time.monotonic()<deadline and 0<=index<len(tree) and index not in seen and depth<21
  seen.add(index);nodes+=1;node=tree[index];assert node['depth']==depth
  u=order[depth];bs=node['branches'];assert [b['family'] for b in bs]==list(range(len(saved[u])))
  for b in bs:
   branches+=1;f=saved[u][b['family']]
   if 'capacity_reject' in b:
    s=b['capacity_reject']+7;assert s in f and usage.get(s,0)>=capacity[s]
   elif 'common_neighbour_reject' in b:
    v=b['common_neighbour_reject'];assert v in chosen and len(f&chosen[v])+len(g[u]&g[v])>1
   else:
    assert set(b)=={'family','child'}
    assert all(usage.get(s,0)<capacity[s] for s in f)
    assert all(len(f&h)+len(g[u]&g[v])<=1 for v,h in chosen.items())
    nxt=usage.copy()
    for s in f:nxt[s]=nxt.get(s,0)+1
    visit(b['child'],depth+1,chosen|{u:f},nxt)
 visit(0,0,{},{});assert len(seen)==len(tree)==cert['nodes']<=10000
 return nodes,branches
