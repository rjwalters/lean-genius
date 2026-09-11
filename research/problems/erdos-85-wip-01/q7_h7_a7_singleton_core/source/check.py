import pathlib,itertools,json,time,math,hashlib,collections
P=pathlib.Path(__file__).parent;edges=list(itertools.combinations(range(7),2));ei={e:i for i,e in enumerate(edges)};perms=list(itertools.permutations(range(7)))
start=time.monotonic();seen=set();classes=[];tested=0;valid=collections.Counter();status='COMPLETE'
try:
 for m in range(7,11):
  for chosen in itertools.combinations(range(21),m):
   tested+=1
   if tested%1000==0 and time.monotonic()-start>60:raise TimeoutError
   g=[0]*7
   for e in chosen:
    u,v=edges[e];g[u]|=1<<v;g[v]|=1<<u
   if max(x.bit_count() for x in g)>3:continue
   if any((g[u]&g[v]).bit_count()>1 for u in range(7) for v in range(u)):continue
   valid[m]+=1;mask=sum(1<<e for e in chosen)
   if mask in seen:continue
   orbit=set()
   for perm in perms:
    orbit.add(sum(1<<ei[tuple(sorted((perm[edges[e][0]],perm[edges[e][1]])))] for e in chosen))
   assert not seen&orbit;seen|=orbit
   classes.append({'edges':[edges[e] for e in chosen],'edge_count':m,'degree_sequence':sorted(x.bit_count() for x in g),'orbit_size':len(orbit),'leaf_leaf_edges':m-7,'leaf_attachment_counts':[3-x.bit_count() for x in g]})
except TimeoutError:status='UNKNOWN'
if status=='COMPLETE':
 assert tested==sum(math.comb(21,m) for m in range(7,11))
 assert sum(valid.values())==len(seen)==sum(r['orbit_size'] for r in classes)
r={'status':status,'tested':tested,'valid_labelled_by_edges':dict(valid),'classes_by_edges':dict(collections.Counter(r['edge_count'] for r in classes)),'classes':classes,'seconds':time.monotonic()-start,'scope':'Conditional a7 singleton core cover assuming each high has singleton-empty incidence3. Fixed full labelled graph universe; no graph completion, colour placement, capped retry or global/Lean exclusion.'}
(P/'results.json').write_text(json.dumps(r,indent=2)+'\n');print({k:v for k,v in r.items() if k!='classes'})
