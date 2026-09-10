import pathlib,json,itertools,hashlib
P=pathlib.Path('/tmp/erdos85-sol1-h7-pair-host-reduction');S=pathlib.Path('/tmp/erdos85-sol1-h7-high0-cover/results.json');load=lambda p:json.loads(p.read_text())
for f,h in load(P/'pins.json').items():assert hashlib.sha256((P/f).read_bytes()).hexdigest()==h
r=load(P/'results.json');assert hashlib.sha256(S.read_bytes()).hexdigest()==r['source_sha256'];seed=load(S);names=seed['names'];idx={n:i for i,n in enumerate(names)};audits=[]
for row in r['results']:
 initial=next(s for s in seed['patterns'] if s['twins_adjacent']==row['twins_adjacent']);g=list(map(set,row['adjacency']));base=list(map(set,initial['adjacency']));hosts=[idx[n] for n in row['hosts']]
 assert row['status']=='SAMPLE' and len(g)==49
 assert all(u in g[v] for u,ns in enumerate(g) for v in ns)
 assert all(len(g[u]&g[v])<=1 for u,v in itertools.combinations(range(49),2))
 assert all(base[u]<=g[u] for u in range(49))
 assert all(len(g[u])==8 for u in range(7)) and all(len(g[u])==7 for u in hosts)
 assert all(len(g[u]&g[0])==1 for u in range(1,49))
 offsets=[];local_profiles=[]
 for i,h in enumerate(hosts):
  mate=(base[h]&set(hosts)).pop();available=set(range(1,7))-(base[mate]&set(range(7)));capacity=7-len(base[h]);delta=len(available)-capacity;offsets.append(delta)
  assert sorted(available)==row['available_colours'][i] and delta==row['offsets'][i]
  guests=g[h]-base[h];ps=[v for v in guests if len(g[v]&set(range(7)))==2];ss=[v for v in guests if len(g[v]&set(range(7)))==1];es=[v for v in guests if not g[v]&set(range(7))]
  assert len(es)==len(ps)-delta and len(ss)==len(available)-2*len(ps)
  occupied=[c for v in ps for c in g[v]&set(range(7))];assert len(set(occupied))==len(occupied) and set(occupied)<=available
  possible=set();pairs=list(itertools.combinations(available,2))
  for n in range(4):
   for matching in itertools.combinations(pairs,n):
    endpoints=[v for e in matching for v in e]
    if len(set(endpoints))!=len(endpoints):continue
    empty=capacity-n-(len(available)-2*n)
    if empty>=0:possible.add(n)
  assert possible==set(range(row['pair_min'][i],row['pair_max'][i]+1));local_profiles.append(sorted(possible))
 assert sum(offsets)==8
 for c in range(1,7):
  slots=[h for h in hosts if not base[h]&base[c]];assert len(slots)==7
  pair_hosts={next(iter(g[v]&set(hosts))) for v in range(7,49) if len(g[v]&set(range(7)))==2 and c in g[v] and 0 not in g[v]};assert len(pair_hosts)==5
  singleton_hosts={next(iter(g[v]&set(hosts))) for v in range(7,49) if g[v]&set(range(7))=={c}};assert singleton_hosts==set(slots)-pair_hosts and len(singleton_hosts)==2
 audits.append(dict(twins_adjacent=row['twins_adjacent'],offsets=offsets,local_pair_counts=local_profiles))
out=dict(status='PASS',audits=audits,scope='Universal necessary pair-host parametrization and exact singleton/empty naming; two sample partial graphs only, no colouring census or H7 exclusion',method='Direct support/degree reconstruction, independent local matching-subset enumeration and full49 graph checks')
print(out);pathlib.Path(__file__).with_name('REVIEW2066.json').write_text(json.dumps(out,indent=2)+'\n')
