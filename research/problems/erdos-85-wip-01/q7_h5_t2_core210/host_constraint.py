import itertools,time
masks=[7,25,10,18,12,20]+[0]*12
caps=[6,5,5,5,5]
def feasible(G,deadline):
 for c in range(5):
  if time.monotonic()>deadline:raise TimeoutError
  required=[v for v in range(5,23) if not G[v]&G[c]];heavy=[v for v in required if v<11];empty=[v for v in required if v>=11];groups=[]
  for k in range(3):
   for hs in itertools.combinations(heavy,k):
    w=sum(masks[v-5].bit_count() for v in hs)
    if w>5 or any(G[u]&G[v] for u,v in itertools.combinations(hs,2)):continue
    for q in range(min(len(empty),1+w-k)+1):
     for es in itertools.combinations(empty,q):
      group=hs+es
      if group and all(not G[u]&G[v] for u,v in itertools.combinations(group,2)):groups.append(sum(1<<v for v in group))
  full=sum(1<<v for v in required);by={v:[g for g in groups if g>>v&1] for v in required};failed=set()
  def solve(left,bins):
   if time.monotonic()>deadline:raise TimeoutError
   if not left:return True
   if not bins or (left,bins) in failed:return False
   options=None
   for v in required:
    if not left>>v&1:continue
    choices=[g for g in by[v] if g&left==g]
    if not choices:return False
    if options is None or len(choices)<len(options):options=choices
   for g in sorted(options,key=int.bit_count,reverse=True):
    if solve(left^g,bins-1):return True
   failed.add((left,bins));return False
  if not solve(full,caps[c]):return False
 return True
