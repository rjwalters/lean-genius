from pathlib import Path
import itertools,json,collections,time,math
P=Path(__file__).parent;K=list(itertools.combinations(range(7),2));ki={e:i for i,e in enumerate(K)};perms=list(itertools.permutations(range(7)));start=time.monotonic();raw=set()
for es in itertools.combinations(range(21),6):
 g=[0]*7
 for e in es:
  u,v=K[e];g[u]|=1<<v;g[v]|=1<<u
 if max(x.bit_count() for x in g)>3 or any((g[u]&g[v]).bit_count()>1 for u in range(7) for v in range(u)):continue
 raw.add(sum(1<<e for e in es))
seen=set();Freps=[]
for mask in sorted(raw):
 if mask in seen:continue
 edges=[K[e] for e in range(21) if mask>>e&1]
 orbit={sum(1<<ki[tuple(sorted((p[u],p[v])))] for u,v in edges) for p in perms}
 assert not orbit&seen and orbit<=raw;seen|=orbit;Freps.append({'edges':edges,'orbit_size':len(orbit),'mask':mask})
assert seen==raw
cases=[];Xtested=0
for fi,r in enumerate(Freps):
 F=set(r['edges']);fg=[set() for _ in range(7)]
 for u,v in F:fg[u].add(v);fg[v].add(u)
 allowed=[e for e in K if not fg[e[0]]&fg[e[1]]];ei={e:i for i,e in enumerate(allowed)};caps=[7-2*len(ns) for ns in fg]
 actions=[p for p in perms if {tuple(sorted((p[u],p[v]))) for u,v in F}==F];Xraw=set()
 for chosen in itertools.combinations(range(len(allowed)),11):
  Xtested+=1
  if time.monotonic()-start>60:raise TimeoutError
  deg=[sum(x in allowed[e] for e in chosen) for x in range(7)]
  if any(deg[x]>caps[x] for x in range(7)):continue
  Xraw.add(sum(1<<e for e in chosen))
 Xseen=set();reps=[]
 for mask in sorted(Xraw):
  if mask in Xseen:continue
  edges=[allowed[e] for e in range(len(allowed)) if mask>>e&1]
  orbit={sum(1<<ei[tuple(sorted((p[u],p[v])))] for u,v in edges) for p in actions}
  assert orbit<=Xraw and not orbit&Xseen;Xseen|=orbit
  hosts=[list(e) for e in edges]
  for x in range(7):hosts.extend([[x]]*(caps[x]-sum(x in e for e in edges)))
  assert len(hosts)==14 and sum(len(h)==1 for h in hosts)==3
  base=[set() for _ in range(21)]
  for u,v in F:base[u].add(v);base[v].add(u)
  for u,h in enumerate(hosts,7):
   for x in h:base[u].add(x);base[x].add(u)
  assert all(len(base[u]&base[v])<=1 for u in range(21) for v in range(u))
  assert all(len(base[x])==7-len(fg[x]) for x in range(7))
  reps.append({'X_edges':edges,'mask':mask,'orbit_size':len(orbit),'singleton_hosts':hosts})
 assert Xseen==Xraw
 cases.append({'F_index':fi,'F_edges':sorted(F),'F_orbit_size':r['orbit_size'],'AutF_order':len(actions),'allowed':allowed,'raw_X':len(Xraw),'X_orbits':len(reps),'representatives':reps})
r={'status':'COMPLETE','F_labelled':len(raw),'F_orbits':len(Freps),'X_subsets_tested':Xtested,'X_labelled_total':sum(r['raw_X'] for r in cases),'X_orbits_total':sum(r['X_orbits'] for r in cases),'positive_F':sum(bool(r['raw_X']) for r in cases),'cases':cases,'seconds':time.monotonic()-start,'scope':'a6 exact E/S-host projection with11double-host leaves and3single-host cores, no high/P/S-edge completion. No oldcappedhosttree retry.'};(P/'cover-results.json').write_text(json.dumps(r,indent=2)+'\n');print({k:v for k,v in r.items() if k!='cases'})
