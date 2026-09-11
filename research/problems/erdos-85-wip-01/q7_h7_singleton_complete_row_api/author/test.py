import pathlib,json,gzip,itertools,time,hashlib,collections
from filter import check,validate,complete_domains,arc_consistency,Budget
P=pathlib.Path(__file__).parent;S=P.parent/'h7-a7-empty-first-singleton-rows';start=time.monotonic()
with gzip.open(S/'results.json.gz','rt') as f:bases=json.load(f)['results']
completions=json.loads((S/'completion-results.json').read_text())['results'];fixtures=[]
for c in completions:
 for edges in c['solutions']:
  g=[set(ns) for ns in bases[c['source_index']]['adjacency']]
  for u,v in edges:g[u].add(v);g[v].add(u)
  fixtures.append([sorted(ns) for ns in g])
assert len(fixtures)==33
(P/'fixtures.json').write_text(json.dumps(fixtures)+'\n')
def matchings(xs):
 if not xs:yield [];return
 a=xs[0]
 for k in range(1,len(xs)):
  for tail in matchings(xs[1:k]+xs[k+1:]):yield [(a,xs[k])]+tail
out=[];receipts=[];rowschecked=failed=0
for index,adj in enumerate(fixtures):
 assert time.monotonic()-start<60
 g=list(map(set,adj));gm,support,E,U=validate(adj);full=complete_domains(gm,support,U,Budget(100000,time.monotonic()+60));assert full['status']=='DOMAINS_COMPLETE'
 singles={h:[v for v in U if support[v]==1<<h] for h in range(7)};pairs={tuple(h for h in range(7) if support[v]>>h&1):v for v in U if support[v].bit_count()==2}
 for u in U:
  need=7-len(g[u]);missing=[h for h in range(7) if not g[u]&g[h]];assert len(missing) in [4,6,7];np=len(missing)-need;answer=set()
  for pc in itertools.combinations(missing,2*np):
   sc=[h for h in missing if h not in pc]
   if support[u].bit_count()==1 and sc:continue
   for pm in matchings(list(pc)):
    pv=[pairs[tuple(sorted(e))] for e in pm]
    for sv in itertools.product(*(singles[h] for h in sc)):
     row=set(pv)|set(sv)
     if u in row or row&g[u]:continue
     ns=g[u]|row
     if len(ns)!=7 or any(len(ns&g[h])!=1 for h in range(7)):continue
     if any((g[v]-{u})&(g[w]-{u}) for v,w in itertools.combinations(ns,2)):continue
     answer.add(sum(1<<v for v in row))
  assert answer==set(full['initial'][u]),(index,u,len(answer),len(full['initial'][u]));rowschecked+=len(answer)
 r=check(adj,max_nodes=100000,deadline=time.monotonic()+60);receipts.append(r)
 if r['status']=='INFEASIBLE_ROW':assert not r['initial'][r['empty_vertex']]
 if r['status']=='INFEASIBLE_ARC':
  domains={u:set(ms) for u,ms in r['initial'].items()}
  for e in r['events']:
   u,v=e['vertex'],e['against'];removed=set(e['removed']);assert removed<=domains[u]
   for a in removed:
    aa=g[u]|{w for w in U if a>>w&1}
    for b in domains[v]:
     bb=g[v]|{w for w in U if b>>w&1};assert ((v in aa)!=(u in bb)) or len(aa&bb)>1;failed+=1
   domains[u]-=removed
  assert not domains[r['empty_vertex']]
 assert check(adj,max_nodes=0)['status']=='UNKNOWN' and check(adj,deadline=time.monotonic()-1)['status']=='UNKNOWN'
 bad=[list(ns) for ns in adj];bad[0].append(0)
 try:check(bad);raise AssertionError('invalid accepted')
 except ValueError:pass
 out.append(dict(index=index,status=r['status'],nodes=r['nodes'],generation_nodes=full['nodes']))
g=[0]*49
batch=arc_consistency(g,{7:[1<<8,(1<<8)|(1<<9)],8:[0]},Budget(1,None));assert batch['status']=='UNKNOWN' and not batch['events'] and batch['remaining'][7]==[1<<8,(1<<8)|(1<<9)]
(P/'receipts.json').write_text(json.dumps(receipts,indent=2)+'\n');r=dict(status='PASS',fixtures=33,domains=33*35,rows=rowschecked,failedsupports=failed,counts=dict(collections.Counter(x['status'] for x in out)),seconds=time.monotonic()-start,results=out);(P/'results.json').write_text(json.dumps(r,indent=2)+'\n');print({k:v for k,v in r.items() if k!='results'})
