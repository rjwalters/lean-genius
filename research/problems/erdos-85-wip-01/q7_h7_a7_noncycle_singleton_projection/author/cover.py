import pathlib,json,itertools,time,collections,sqlite3,hashlib
P=pathlib.Path(__file__).parent;A=pathlib.Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3/h7-a7-singleton-core');assert not (P/'results.json').exists()
c=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True);c.row_factory=sqlite3.Row;prem=[]
for rid in [2090,2091,2097,2107]:
 r=dict(c.execute('select * from review_requests where id=?',(rid,)).fetchone());assert r['resolution'].startswith('PASS');prem.append(r)
(P/'premises.json').write_text(json.dumps(prem,indent=2)+'\n');(P/'source.json').write_bytes((A/'results.json').read_bytes());source=json.loads((P/'source.json').read_text());cases=[(i,r) for i,r in enumerate(source['classes']) if r['edge_count']==7 and r['degree_sequence']!=[2]*7];assert len(cases)==14
K=list(itertools.combinations(range(7),2));summaries=[];reps=[];start=time.monotonic()
for fi,f in cases:
 F=set(map(tuple,f['edges']));fg=[{v for v in range(7) if tuple(sorted((u,v))) in F} for u in range(7)];capacity=[7-2*len(ns) for ns in fg];allowed=[e for e in K if not fg[e[0]]&fg[e[1]]];assert len(allowed)<=13
 ix={e:i for i,e in enumerate(allowed)};actions=[]
 for p in itertools.permutations(range(7)):
  if {tuple(sorted((p[a],p[b]))) for a,b in F}==F:actions.append([ix[tuple(sorted((p[a],p[b])))] for a,b in allowed])
 raw=set();examined=0
 for es in itertools.combinations(range(len(allowed)),7):
  examined+=1;assert examined<=100000 and time.monotonic()-start<60
  degrees=[sum(u in allowed[e] for e in es) for u in range(7)]
  if all(d<=cap for d,cap in zip(degrees,capacity)):raw.add(sum(1<<e for e in es))
 seen=set();classreps=[]
 for m in sorted(raw):
  if m in seen:continue
  orbit={sum(1<<a[e] for e in range(len(allowed)) if m>>e&1) for a in actions};assert orbit<=raw and not seen&orbit;seen|=orbit
  edges=[allowed[e] for e in range(len(allowed)) if m>>e&1];hosts=list(edges)
  for u in range(7):hosts.extend([(u,)]*(capacity[u]-sum(u in e for e in edges)))
  assert len(hosts)==14 and sum(len(h)==1 for h in hosts)==7
  g=[set() for _ in range(21)]
  for u,v in F:g[u].add(v);g[v].add(u)
  for s,h in enumerate(hosts,7):
   for e in h:g[s].add(e);g[e].add(s)
  assert all(len(g[e])==7-len(fg[e]) for e in range(7)) and all(len(g[u]&g[v])<=1 for u in range(21) for v in range(u))
  r=dict(F_index=fi,F_edges=sorted(F),mask=m,edges=edges,orbit_size=len(orbit),singleton_hosts=hosts);classreps.append(r);reps.append(r)
 assert seen==raw
 summaries.append(dict(F_index=fi,F_edges=sorted(F),capacity=capacity,allowed=len(allowed),examined=examined,raw=len(raw),orbits=len(classreps),aut_F=len(actions),orbit_histogram=dict(collections.Counter(r['orbit_size'] for r in classreps))))
r=dict(status='COMPLETE',F_classes=summaries,representatives=reps,seconds=time.monotonic()-start,scope='14 noncycle a7 emptyF shapes from accepted2090 graph-class cover. Necessary E/S host projection only; no oldcycle/cappedtree retry.')
(P/'results.json').write_text(json.dumps(r,indent=2)+'\n');print(summaries);print('total orbits',len(reps))
