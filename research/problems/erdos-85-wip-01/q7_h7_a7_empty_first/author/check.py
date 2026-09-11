import pathlib,itertools,json,time
P=pathlib.Path(__file__).parent;hi=list(range(7));K=list(itertools.combinations(hi,2));Rcases=[{tuple(sorted((i,(i+1)%7))) for i in hi},{(0,1),(0,2),(1,2),(3,4),(4,5),(5,6),(3,6)}];Fcases=[Rcases[0],{(0,1),(0,2),(1,2),(3,4),(3,5),(4,5),(5,6)}];out=[];start=time.monotonic()
for ri,R in enumerate(Rcases):
 Q=[e for e in K if e not in R];assert len(Q)==14
 for fi,F in enumerate(Fcases):
  fg=[set() for _ in hi]
  for u,v in F:fg[u].add(v);fg[v].add(u)
  assert len(F)==7 and max(map(len,fg))<=3 and all(len(fg[u]&fg[v])<=1 for u in hi for v in range(u))
  # One proper edge-colouring witness only, never an exhaustive graph claim.
  domains=[]
  for x in hi:
   d=len(fg[x]);domains.append([sum(1<<e for e in choice) for choice in itertools.combinations(range(14),d) if len({v for e in choice for v in Q[e]})==2*d])
  order=sorted(hi,key=lambda x:(len(domains[x]),x));nodes=0
  def colour(k,used,blocks):
   global nodes
   nodes+=1
   if nodes>100000 or time.monotonic()-start>60:raise TimeoutError
   if k==7:return blocks
   x=order[k]
   for m in domains[x]:
    if not m&used:
     b=dict(blocks);b[x]=m;answer=colour(k+1,used|m,b)
     if answer is not None:return answer
   return None
  blocks=colour(0,0,{});assert blocks is not None
  phi={Q[e]:x for x,m in blocks.items() for e in range(14) if m>>e&1};assert len(phi)==14
  unused=[set(hi)-{phi[e] for e in Q if i in e} for i in hi];assert all(len(u)==3 for u in unused)
  choices=[list(itertools.combinations(sorted(u),2)) for u in unused];good=0;total=0;witness=None
  for selected in itertools.product(*choices):
   total+=1;predicted=len(set(selected))==7 and all(not fg[x]&fg[y] for x,y in selected)
   g=[set() for _ in range(49)]
   def edge(u,v):g[u].add(v);g[v].add(u)
   for i in hi:edge(i,7+2*i);edge(i,8+2*i)
   for k,(i,j) in enumerate(K):
    edge(i,21+k);edge(j,21+k)
    if (i,j) in phi:edge(21+k,42+phi[i,j])
   for x,y in F:edge(42+x,42+y)
   for i,pair in enumerate(selected):
    for x in pair:edge(7+2*i,42+x)
    edge(8+2*i,42+next(iter(unused[i]-set(pair))))
   assert all(len(g[i])==8 for i in hi) and all(len(g[e])==7 for e in range(42,49))
   assert all(len(g[i]&g[e])==1 for i in hi for e in range(42,49))
   actual=all(len(g[u]&g[v])<=1 for u in range(49) for v in range(u));assert actual==predicted
   if actual:good+=1;witness=selected
  # Independently count distinct representatives with subset-of-pairs DP.
  pair_index={e:k for k,e in enumerate(K)};dp={0:1}
  for options in choices:
   nxt={}
   for used,count in dp.items():
    for x,y in options:
     bit=1<<pair_index[x,y]
     if not used&bit and not fg[x]&fg[y]:nxt[used|bit]=nxt.get(used|bit,0)+count
   dp=nxt
  assert sum(dp.values())==good
  out.append(dict(R_case=ri,F_case=fi,colour_witness_nodes=nodes,phi=[[list(e),x] for e,x in sorted(phi.items())],unused=list(map(sorted,unused)),all_choices_tested=total,c4_free_choices=good,matching_count=sum(dp.values()),witness=witness))
(P/'results.json').write_text(json.dumps(dict(status='PASS',fixtures=out,seconds=time.monotonic()-start,scope='Four fixed proper-colouring witnesses; exhaustive2187singleton choices each verifies exact partial-C4/SDR equivalence, no class exclusion.'),indent=2)+'\n');print([(r['R_case'],r['F_case'],r['c4_free_choices']) for r in out])
