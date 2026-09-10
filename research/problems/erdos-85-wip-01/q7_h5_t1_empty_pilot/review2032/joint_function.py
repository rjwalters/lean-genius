import itertools
def feasible(masks,adj,capacities):
 n=len(masks);pairlist=list(itertools.combinations(range(n),2));pairid={p:i for i,p in enumerate(pairlist)};choices=[]
 for colour in range(5):
  required=[v for v in range(n) if sum(bool(masks[w]>>colour&1) for w in adj[v])==0]
  k=max(0,len(required)-capacities[colour])
  if 2*k>len(required):return False
  allowed=[(u,v) for u,v in itertools.combinations(required,2) if not(masks[u]&masks[v]) and not(adj[u]&adj[v])]
  options=[]
  for matching in itertools.combinations(allowed,k):
   vertices=[v for edge in matching for v in edge]
   if len(set(vertices))==2*k:options.append(sum(1<<pairid[e] for e in matching))
  if not options:return False
  choices.append(options)
 choices.sort(key=len);states={0}
 for options in choices:
  states={old|option for old in states for option in options if not old&option}
  if not states:return False
 return True

