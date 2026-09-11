import pathlib,itertools,json,collections,time
P=pathlib.Path(__file__).parent;start=time.monotonic();V=range(7);K=list(itertools.combinations(V,2));F={tuple(sorted((i,(i+1)%7))) for i in V};fg=[{j for j in V if tuple(sorted((i,j))) in F} for i in V];allowed=[e for e in K if not fg[e[0]]&fg[e[1]]];assert len(allowed)==14
idx={e:i for i,e in enumerate(allowed)};actions=[]
for p in itertools.permutations(V):
 if {tuple(sorted((p[x],p[y]))) for x,y in F}==F:actions.append([idx[tuple(sorted((p[x],p[y])))] for x,y in allowed])
assert len(actions)==14
raw=set();examined=0
for es in itertools.combinations(range(14),7):
 examined+=1;assert examined<=100000 and time.monotonic()-start<60
 d=[sum(i in allowed[e] for e in es) for i in V]
 if max(d)<=3:raw.add(sum(1<<e for e in es))
seen=set();reps=[]
for m in sorted(raw):
 if m in seen:continue
 orbit={sum(1<<a[e] for e in range(14) if m>>e&1) for a in actions};assert orbit<=raw and not orbit&seen;seen|=orbit
 edges=[allowed[e] for e in range(14) if m>>e&1];hosts=[tuple(e) for e in edges]
 for x in V:hosts.extend([(x,)]*(3-sum(x in e for e in edges)))
 assert len(hosts)==14 and sum(len(h)==1 for h in hosts)==7
 g=[set() for _ in range(21)]
 for x,y in F:g[x].add(y);g[y].add(x)
 for i,h in enumerate(hosts,7):
  for x in h:g[i].add(x);g[x].add(i)
 assert all(len(g[x])==5 for x in V) and all(len(g[u]&g[v])<=1 for u in range(21) for v in range(u))
 reps.append(dict(mask=m,edges=edges,orbit_size=len(orbit),singleton_hosts=hosts))
assert seen==raw
r=dict(status='COMPLETE',examined=examined,raw_count=len(raw),orbits=len(reps),orbit_histogram=dict(collections.Counter(r['orbit_size'] for r in reps)),F_edges=sorted(F),allowed=allowed,representatives=reps,seconds=time.monotonic()-start,scope='Necessary E/S-host projection only for a7 F=C7; high and pair vertices omitted. No full graph exclusion.')
(P/'results.json').write_text(json.dumps(r,indent=2)+'\n');print({k:v for k,v in r.items() if k!='representatives'})
