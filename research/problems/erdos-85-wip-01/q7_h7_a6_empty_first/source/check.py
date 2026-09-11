from pathlib import Path
import json,itertools,time,collections
P=Path(__file__).parent;H=list(range(7));K=list(itertools.combinations(H,2));cycle={tuple(sorted((i,(i+1)%7))) for i in H};Rcases=[cycle|{(0,2),(3,5)},cycle|{(0,3),(1,4)}];Fcases=[{(i,i+1) for i in range(6)},{(0,1),(0,2),(1,3),(1,4),(2,5),(2,6)}];out=[];start=time.monotonic()
for ri,R in enumerate(Rcases):
 Q=[e for e in K if e not in R];assert len(Q)==12
 assert sorted(sum(i in e for e in R) for i in H)==[2]*3+[3]*4
 for fi,F in enumerate(Fcases):
  fg=[set() for _ in H]
  for x,y in F:fg[x].add(y);fg[y].add(x)
  assert len(F)==6 and max(map(len,fg))<=3 and all(len(fg[u]&fg[v])<=1 for u in H for v in range(u))
  domains=[]
  for x in H:
   d=len(fg[x]);domains.append([sum(1<<e for e in chosen) for chosen in itertools.combinations(range(12),d) if len({v for e in chosen for v in Q[e]})==2*d])
  order=sorted(H,key=lambda x:(len(domains[x]),x));nodes=0
  def colour(k,used,blocks):
   global nodes
   nodes+=1
   if nodes>100000 or time.monotonic()-start>60:raise TimeoutError
   if k==7:return blocks
   x=order[k]
   for m in domains[x]:
    if not m&used:
     answer=colour(k+1,used|m,blocks+[(x,m)])
     if answer is not None:return answer
   return None
  blocks=colour(0,0,[]);assert blocks is not None
  phi={Q[e]:x for x,m in blocks for e in range(12) if m>>e&1};assert len(phi)==12
  unused=[sorted(set(H)-{phi[e] for e in Q if i in e}) for i in H];assert sorted(map(len,unused))==[3]*3+[4]*4
  choices=[]
  for U in unused:
   if len(U)==3:row=[(tuple(x for x in U if x!=single),(single,)) for single in U]
   else:row=[((U[0],mate),tuple(x for x in U if x not in (U[0],mate))) for mate in U[1:]]
   assert len(row)==3;choices.append(row)
  total=good=0;witness=None
  for selected in itertools.product(*choices):
   total+=1;pairs=[tuple(sorted(block)) for row in selected for block in row if len(block)==2];assert len(pairs)==11
   predicted=len(set(pairs))==11 and all(not fg[x]&fg[y] for x,y in pairs)
   g=[set() for _ in range(49)]
   def edge(u,v):g[u].add(v);g[v].add(u)
   for i,row in enumerate(selected):
    for j,block in enumerate(row):
     s=7+2*i+j;edge(i,s)
     for x in block:edge(s,42+x)
   for k,(i,j) in enumerate(K):
    edge(i,21+k);edge(j,21+k)
    if (i,j) in phi:edge(21+k,42+phi[i,j])
   for x,y in F:edge(42+x,42+y)
   assert all(len(g[i])==8 for i in H) and all(len(g[x])==7 for x in range(42,49))
   assert all(len(g[i]&g[x])==1 for i in H for x in range(42,49))
   actual=all(len(g[u]&g[v])<=1 for u in range(49) for v in range(u));assert actual==predicted
   if actual:good+=1;witness=selected
  # Independent subset packing DP, each high selects one or two pair-values.
  pi={e:i for i,e in enumerate(K)};dp={0:1}
  for row in choices:
   values=[]
   for choice in row:
    pairs=[tuple(sorted(block)) for block in choice if len(block)==2]
    if any(fg[x]&fg[y] for x,y in pairs):continue
    values.append(sum(1<<pi[pair] for pair in pairs))
   nxt=collections.Counter()
   for used,n in dp.items():
    for mask in values:
     if not used&mask:nxt[used|mask]+=n
   dp=nxt
  assert sum(dp.values())==good
  out.append({'R_edges':sorted(R),'F_edges':sorted(F),'colour_witness_nodes':nodes,'phi':[[list(e),x] for e,x in sorted(phi.items())],'unused':unused,'choices':choices,'tested':total,'c4_free_choices':good,'packing_count':sum(dp.values()),'witness':witness})
r={'status':'PASS','fixtures':out,'seconds':time.monotonic()-start,'scope':'Four fixed proper-colouring fixtures, each2187 canonical singleton choices. Exact partialC4/pair-packing equivalence only; no R/Fclass,fullcolouring,H7 or Lean/global exclusion; no cappedhosttree retry.'}
(P/'results.json').write_text(json.dumps(r,indent=2)+'\n');print([(r['tested'],r['c4_free_choices'],r['colour_witness_nodes']) for r in out])
