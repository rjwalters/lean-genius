import itertools,time

def possible(G,deadline):
 G=[set(x) for x in G]+[set() for _ in range(49-len(G))]; high=set(range(5));nonempty=list(range(5,35)); demand=[7-len(G[v]) for v in nonempty];pools=[[v for v,d in zip(nonempty,demand) if d and c in G[v]] for c in range(5)];rows=set()
 for choices in itertools.product(*pools):
  if time.monotonic()>deadline:raise TimeoutError
  row=frozenset(choices)
  if sum(len(G[v]&high) for v in row)!=5:continue
  if any(G[u]&G[v] for u,v in itertools.combinations(row,2)):continue
  rows.add(tuple(sorted(v-5 for v in row)))
 rows=sorted(rows);pairs=[set(itertools.combinations(r,2)) for r in rows]
 def covers(indices,remaining,selected,used_pairs):
  if time.monotonic()>deadline:raise TimeoutError
  if not any(remaining):
   if len(selected)!=14:return False
   A=[set(x) for x in G]
   for e,i in enumerate(selected,35):
    for v in rows[i]:A[e].add(v+5);A[v+5].add(e)
   for u in range(35,49):
    legal=0
    for v in range(35,49):
     if u==v:continue
     A[u].add(v);A[v].add(u)
     good=all(len(A[a]&A[b])<=1 for a,b in itertools.combinations(range(49),2))
     A[u].remove(v);A[v].remove(u)
     legal+=good
    if legal<7-len(A[u]):return False
   return True
  if len(selected)>=14:return False
  indices=[i for i in indices if not pairs[i]&used_pairs and all(remaining[v] for v in rows[i])]
  for v,d in enumerate(remaining):
   if d>sum(v in rows[i] for i in indices):return False
  if len(indices)<14-len(selected):return False
  if not indices:return False
  i=indices[0];rest=indices[1:];d=remaining.copy()
  for v in rows[i]:d[v]-=1
  if covers(rest,d,selected+[i],used_pairs|pairs[i]):return True
  return covers(rest,remaining,selected,used_pairs)
 return covers(list(range(len(rows))),demand,[],set())
