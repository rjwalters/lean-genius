import pathlib,json,itertools,hashlib,time,collections
P=pathlib.Path(__file__).parent;cover=json.loads((P/'results.json').read_text());done=json.loads((P/'completion-results.json').read_text());start=time.monotonic();out=[]
for f in cover['F_classes']:
 F=set(map(tuple,f['F_edges']));N=[{v for v in range(7) if tuple(sorted((u,v))) in F} for u in range(7)];allowed=[e for e in itertools.combinations(range(7),2) if not N[e[0]]&N[e[1]]];idx={e:i for i,e in enumerate(allowed)};raw=set()
 for mask in range(1<<len(allowed)):
  if mask.bit_count()!=7:continue
  if all(sum(bool(mask>>i&1) for i,e in enumerate(allowed) if u in e)<=7-2*len(N[u]) for u in range(7)):raw.add(mask)
 aut=[p for p in itertools.permutations(range(7)) if {tuple(sorted((p[u],p[v]))) for u,v in F}==F];seen=set()
 for r in (r for r in cover['representatives'] if r['F_index']==f['F_index']):
  orbit={sum(1<<idx[tuple(sorted((p[u],p[v])))] for u,v in r['edges']) for p in aut};assert not seen&orbit and orbit<=raw and len(orbit)==r['orbit_size'];seen|=orbit
 assert seen==raw and len(raw)==f['raw'];out.append(dict(F_index=f['F_index'],raw=len(raw),orbits=f['orbits']))
valid=0;nodes=[]
for i,r in enumerate(done['results']):
 assert r['source_index']==i and r['F_index']==cover['representatives'][i]['F_index'];rep=cover['representatives'][i];base=[set() for _ in range(21)]
 for u,v in rep['F_edges']:base[u].add(v);base[v].add(u)
 for s,hs in enumerate(rep['singleton_hosts'],7):
  for e in hs:base[s].add(e);base[e].add(s)
 solutions=set()
 for es in r['solutions']:
  code=tuple(map(tuple,es));assert code not in solutions;solutions.add(code);g=[set(ns) for ns in base]
  for u,v in es:assert 7<=u<v<21;g[u].add(v);g[v].add(u)
  assert len(es)==14 and all(len(g[s])==5-len(base[s]) for s in range(7,21))
  seen=set()
  for ns in g:
   for pair in itertools.combinations(sorted(ns),2):assert pair not in seen;seen.add(pair)
  valid+=1
 assert len(solutions)==r['count'];nodes.append(r['nodes'])
assert len(done['results'])==861 and done['results'][-1]['status']=='UNKNOWN' and all(r['status']=='COMPLETE' for r in done['results'][:-1])
r=dict(status='PASS_COVER_AND_OUTPUT_VALIDITY',F_classes=out,completed_bases=860,unknown_bases=1,unvisited_bases=449,valid_saved_extensions=valid,seconds=time.monotonic()-start,scope='Independent raw subset/orbit verification and validity of all saved S graphs. Completion enumeration not rerun; UNKNOWN/unvisited unchanged. Completeness of terminal cases rests on audited MRV traversal.')
(P/'verification.json').write_text(json.dumps(r,indent=2)+'\n');print({k:v for k,v in r.items() if k!='F_classes'})
