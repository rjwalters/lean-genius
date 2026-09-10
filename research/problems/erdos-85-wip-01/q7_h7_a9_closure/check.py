import pathlib,json,hashlib,collections,itertools
P=pathlib.Path(__file__).parent
load=lambda f:json.loads((P/f).read_text())
reviews={r['id']:r for r in load('reviews.json')};pending=[]
for i,r in reviews.items():
 if r['status']!='resolved':pending.append(i)
 else:assert r['resolution'].startswith('PASS'),(i,r['resolution'])
norm=load('normalization.json');a9=next(r for r in norm['cases'] if r['empty_edges']==9);assert a9['profile_keys']==[[True,6],[False,14]]
profiles=load('profiles.json');assert {(r['twins_adjacent'],r['profile_index']) for r in profiles}=={(True,6),(False,14)}
seeds=load('seeds.json');names=seeds['names'];ix={n:i for i,n in enumerate(names)};hosts=[ix[n] for n in ['S0a','S0b']+['P0'+str(c) for c in range(1,7)]];allcounts={};hashmatches=localchecks=0;proofrows=[]
neg={r['assignment_index']:r for r in load('crossed14-local-negatives.json')['results']};assert len(neg)==32

def gh(g):return hashlib.sha256(json.dumps([sorted(ns) for ns in g],separators=(',',':')).encode()).hexdigest()
for profile in profiles:
 twin=profile['twins_adjacent'];seed=next(r for r in seeds['patterns'] if r['twins_adjacent']==twin);N=2640 if twin else 480
 assert profile['status']=='COMPLETE' and len(profile['assignments'])==N
 endpoints=load('twin6-endpoints.json' if twin else 'crossed14-endpoints.json');assert len(endpoints)==N and {r['assignment_index'] for r in endpoints}==set(range(N))
 counts=collections.Counter(r['endpoint'] for r in endpoints);assert counts==({'LOCAL':61,'ARC':2579} if twin else {'LOCAL':32,'ARC':448});allcounts['twin6' if twin else 'crossed14']=dict(counts)
 for r in endpoints:
  ai=r['assignment_index'];g=list(map(set,seed['adjacency']))
  def edge(u,v):g[u].add(v);g[v].add(u)
  for h,m in zip(hosts,profile['assignments'][ai]):
   for j,(a,b) in enumerate(profile['edge_order']):
    if m>>j&1:edge(h,ix['P'+str(a)+str(b)])
  for c in range(1,7):
   missing=[h for h in hosts if not(g[h]&g[c])];assert len(missing)==2
   for h,s in zip(missing,'ab'):edge(h,ix['S'+str(c)+s])
  e=0
  for h in hosts:
   while len(g[h])<7:edge(h,ix['E'+str(e)]);e+=1
  assert e==7
  digest=gh(g)
  if r['graph_sha256'] is not None:assert digest==r['graph_sha256'];hashmatches+=1
  else:
   assert not twin and r['endpoint']=='LOCAL' and ai in neg and r['vertex']==neg[ai]['vertex']
   # Independently verify the32local cases whose receipt stores no whole graph.
   u=r['vertex'];gm=[sum(1<<v for v in ns) for ns in g];outside=set(range(7,49))-set(hosts);need=7-len(g[u]);covered=0
   for v in g[u]:covered|=gm[v]&127
   candidates=[v for v in sorted(outside-{u}-g[u]) if all(not(g[v]&g[w]) for w in g[u])]
   def row_exists(pos,chosen,coverage):
    if len(chosen)==need:return coverage==127
    if len(candidates)-pos<need-len(chosen):return False
    for j in range(pos,len(candidates)):
     v=candidates[j]
     if coverage&(gm[v]&127) or any(gm[v]&gm[w] for w in chosen):continue
     if row_exists(j+1,chosen+[v],coverage|(gm[v]&127)):return True
    return False
   assert not row_exists(0,[],covered);localchecks+=1
  proofrows.append({'profile':[twin,profile['profile_index']],'assignment_index':ai,'endpoint':r['endpoint'],'reconstructed_graph_sha256':digest})
assert hashmatches==3088 and localchecks==32 and len(proofrows)==3120
cross=load('crossed14-census.json');assert cross['status']=='COMPLETE' and cross['raw_assignments']==3840 and cross['canonical_representatives_checked']==480
twin=load('twin6-census.json');assert twin['status']=='COMPLETE' and twin['raw_count']==twin['disjoint_orbit_union']==125280 and twin['source_representatives']==2640
out={'status':'AWAITING_REVIEW' if pending else 'PASS','pending_reviews':pending,'required_profiles':[[True,6],[False,14]],'total_assignments':3120,'endpoints':allcounts,'reconstructed_graph_hash_matches':hashmatches,'independent_local_rejections':localchecks,'uncovered':0,'duplicate_endpoints':0,'rows':proofrows,'scope':'Conditional mathematical/computational H7a9 closure once all prerequisite reviews accepted. No other a-values, H1, Lean, queue or global Erdős85 claim.'};(P/'results.json').write_text(json.dumps(out,indent=2)+'\n');print({k:v for k,v in out.items() if k!='rows'})
