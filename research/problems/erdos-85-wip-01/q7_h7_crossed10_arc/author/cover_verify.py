import pathlib,json,itertools,time
P=pathlib.Path(__file__).parent
source=json.load(open('/tmp/erdos85-sol1-h7-profile-partitions/remaining-results.json'));r=next(x for x in source['results'] if not x['twins_adjacent'] and x['profile_index']==10)
sd=json.load(open('/tmp/erdos85-sol1-h7-high0-cover/results.json'));base=next(s['adjacency'] for s in sd['patterns'] if not s['twins_adjacent']);names=sd['names'];idx={s:i for i,s in enumerate(names)}
g0=list(map(set,base));H=sorted(g0[0]);edges=list(itertools.combinations(range(1,7),2));assert edges==list(map(tuple,r['edge_order']))
# Derive host colour slots from base graph common-high incidences.
avail=[{c for c in range(1,7) if not g0[h]&g0[c]} for h in H]
pc=r['profile']['pair_counts'];domain=[]
for h in range(8):
 choices=[]
 for es in itertools.combinations(range(15),pc[h]):
  ends=[c for e in es for c in edges[e]]
  if len(set(ends))==len(ends) and set(ends)<=avail[h]:choices.append(sum(1<<e for e in es))
 domain.append(choices)
# Profile fixes colours1,2. Its eight automorphisms permute the two
# unordered matched pairs {3,4},{5,6}, with independent endpoint flips.
actions=[]
for flip_order in (False,True):
 pairs=[(3,4),(5,6)][::(-1 if flip_order else 1)]
 for flips in itertools.product((False,True),repeat=2):
  vals=sum((list(p[::-1] if f else p) for p,f in zip(pairs,flips)),[]);cp=dict(zip(range(1,7),[1,2]+vals));hp=[0,1]+[cp[c]+1 for c in range(1,7)]
  ep=[edges.index(tuple(sorted((cp[a],cp[b])))) for a,b in edges];actions.append((hp,ep))
def canon(a):
 images=[]
 for hp,ep in actions:
  b=[0]*8
  for h,m in enumerate(a):b[hp[h]]=sum(1<<ep[e] for e in range(15) if m>>e&1)
  images.append(tuple(b))
 return min(images)
nodes=0;raw=0;orbits=set();start=time.monotonic()
def dfs(todo,used,a):
 global nodes,raw
 nodes+=1
 if nodes>100000 or time.monotonic()-start>60:raise TimeoutError
 if not todo:
  assert used==32767;raw+=1;orbits.add(canon(a));return
 _,h,opts=min((len(opts),h,opts) for h in todo for opts in [[m for m in domain[h] if not m&used]])
 for m in opts:
  b=a.copy();b[h]=m;dfs(todo-{h},used|m,b)
try:dfs(set(range(8)),0,[0]*8);status='COMPLETE'
except TimeoutError:status='UNKNOWN'
if status=='COMPLETE':assert orbits=={tuple(a) for a in r['assignments']}
cover=dict(status=status,nodes=nodes,raw=raw,orbits=len(orbits),seconds=time.monotonic()-start)
print(cover,flush=True)

(P/'cover-verification.json').write_text(json.dumps(cover,indent=2)+'\n')
