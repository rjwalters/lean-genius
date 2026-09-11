from pathlib import Path
import itertools,json,time,collections
P=Path(__file__).parent;H=tuple(range(7));K=list(itertools.combinations(H,2));Rcases=[{tuple(sorted((i,(i+1)%7))) for i in H},{(0,1),(0,2),(1,2),(3,4),(4,5),(5,6),(3,6)}];out=[];start=time.monotonic()
for ri,R in enumerate(Rcases):
 Q=[e for e in K if e not in R];ei={e:i for i,e in enumerate(Q)};raw=[];nodes=0
 def visit(left,blocks):
  global nodes
  nodes+=1
  if not left:raw.append(tuple(sorted(blocks)));return
  a=left[0]
  for i,b in enumerate(left[1:],1):
   if set(Q[a]).isdisjoint(Q[b]):visit(left[1:i]+left[i+1:],blocks+[(a,b)])
 visit(tuple(range(14)),[]);assert len(set(raw))==len(raw)
 actions=[]
 for perm in itertools.permutations(H):
  if {tuple(sorted((perm[u],perm[v]))) for u,v in R}==R:actions.append([ei[tuple(sorted((perm[u],perm[v])))] for u,v in Q])
 assert len(actions)==[14,48][ri]
 seen=set();reps=[]
 for blocks in raw:
  if blocks in seen:continue
  orbit={tuple(sorted(tuple(sorted((action[a],action[b]))) for a,b in blocks)) for action in actions}
  assert not seen&orbit and orbit<=set(raw)
  seen|=orbit;rep=min(orbit)
  stabilizer=[action for action in actions if tuple(sorted(tuple(sorted((action[a],action[b]))) for a,b in rep))==rep]
  reps.append({'blocks':rep,'orbit_size':len(orbit),'stabilizer_size':len(stabilizer)})
 assert len(seen)==len(raw) and sum(r['orbit_size'] for r in reps)==len(raw)
 out.append({'R_edges':sorted(R),'Q_edges':Q,'aut_R':actions,'recursive_nodes':nodes,'raw_partitions':len(raw),'canonical_partitions':len(reps),'orbit_histogram':dict(collections.Counter(r['orbit_size'] for r in reps)),'representatives':sorted(reps,key=lambda r:r['blocks'])})
r={'status':'COMPLETE','cases':out,'seconds':time.monotonic()-start,'scope':'Complete Qedge pairing cover for proper colouring with all7empty degrees2. No cyclic block-colour placement, singleton incidence or remaining-low completion; no oldcappedhost census retry.'}
(P/'results.json').write_text(json.dumps(r,indent=2)+'\n');print([{k:v for k,v in r.items() if k not in ['aut_R','representatives','Q_edges','R_edges']} for r in out])
