"""Independent set-based necessary-family reconstruction for native certificate audit."""
import itertools

def reconstruct(graph,only=None):
 g=[set(v for v in range(49) if mask>>v&1) for mask in graph]
 H=set(range(7));E=set(range(42,49))
 assert all(g[u]<=H|E and len(g[u]&H)==2 for u in range(21,42))
 assert all(len(g[v]&H)==1 for v in range(7,21))
 assert all(len(g[h])==8 and not g[h]&H for h in H) and all(len(g[e])==7 for e in E)
 demand={u:7-2*len(g[u]) for u in range(21,42)};capacity={v:7-len(g[v]) for v in range(7,21)}
 assert set(demand.values())<={1,3} and set(capacity.values())<={2,3} and sum(demand.values())==sum(capacity.values())==39
 families={}
 def match(left,supports):
  if not left:return True
  v=min(left)
  return any(frozenset([v,w]) in supports and match(left-{v,w},supports) for w in left-{v})
 for u in (demand if only is None else [only]):
  candidates={v for v in capacity if all(g[v].isdisjoint(g[w]) for w in g[u])};choices=[]
  for chosen in itertools.combinations(sorted(candidates),demand[u]):
   if any(g[v]&g[w] for v,w in itertools.combinations(chosen,2)):continue
   used=set().union(*(g[v]&H for v in chosen));assert len(used)==demand[u];left=H-used
   pairs={v for v in demand if v!=u and g[v]&H<=left and all(g[v].isdisjoint(g[w]) for w in g[u]|set(chosen))}
   supports={frozenset(g[v]&H) for v in pairs};assert all(len(e)==2 for e in supports)
   if match(left,supports):choices.append(frozenset(chosen))
  families[u]=choices
 return families,capacity
