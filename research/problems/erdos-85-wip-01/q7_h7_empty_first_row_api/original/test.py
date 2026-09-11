from pathlib import Path
import json,itertools,time,hashlib
from filter import check,validate,complete_domains,arc_consistency,Budget
p=Path(__file__).parent;source=p/'source-fixtures.json';data=json.loads(source.read_text());K=list(itertools.combinations(range(7),2));Fcases=[{tuple(sorted((i,(i+1)%7))) for i in range(7)},{(0,1),(0,2),(1,2),(3,4),(3,5),(4,5),(5,6)}];fixtures=[]
for r in data['fixtures']:
 if not r['witness']:continue
 g=[set() for _ in range(49)]
 def add(u,v):g[u].add(v);g[v].add(u)
 for i in range(7):add(i,7+2*i);add(i,8+2*i)
 phi={tuple(e):x for e,x in r['phi']}
 for k,(i,j) in enumerate(K):
  add(i,21+k);add(j,21+k)
  if (i,j) in phi:add(21+k,42+phi[i,j])
 for x,y in Fcases[r['F_case']]:add(42+x,42+y)
 for i,pair in enumerate(r['witness']):
  for x in pair:add(7+2*i,42+x)
  add(8+2*i,42+next(iter(set(r['unused'][i])-set(pair))))
 fixtures.append([sorted(ns) for ns in g])
(p/'fixtures.json').write_text(json.dumps(fixtures)+'\n')

def pairings(xs):
 if not xs:yield [];return
 a=xs[0]
 for i in range(1,len(xs)):
  for tail in pairings(xs[1:i]+xs[i+1:]):yield [(a,xs[i])]+tail
summaries=[];receipts=[];start=time.monotonic()
for index,adj in enumerate(fixtures):
 g=list(map(set,adj));masks,support,E,U=validate(adj);budget=Budget(100000,time.monotonic()+60);full=complete_domains(masks,support,U,budget);assert full['status']=='DOMAINS_COMPLETE'
 singles={i:[v for v in U if support[v]==1<<i] for i in range(7)};pairs={tuple(i for i in range(7) if support[v]>>i&1):v for v in U if support[v].bit_count()==2};total=0
 for u in U:
  need=7-len(g[u]);answer=set();tested=0
  # Explicit support partitions, independent of the first-colour DFS.
  for pair_colours in itertools.combinations(range(7),2*(7-need)):
   single_colours=[i for i in range(7) if i not in pair_colours]
   for pm in pairings(list(pair_colours)):
    pair_vertices=[pairs[tuple(sorted(e))] for e in pm]
    for sv in itertools.product(*(singles[i] for i in single_colours)):
     tested+=1;row=set(pair_vertices)|set(sv)
     if u in row or row&g[u]:continue
     ns=g[u]|row
     if len(ns)!=7 or any(len(ns&g[h])!=1 for h in range(7)):continue
     if any((g[v]-{u})&(g[w]-{u}) for v,w in itertools.combinations(ns,2)):continue
     answer.add(sum(1<<v for v in row))
  assert tested==({4:210,5:840}[need])
  assert answer==set(full['initial'][u]),(index,u,len(answer),len(full['initial'][u]));total+=len(answer)
 result=check(adj,max_nodes=100000,deadline=time.monotonic()+60)
 receipts.append(result)
 if result['status']=='INFEASIBLE_ROW':assert not result['initial'][result['empty_vertex']]
 if result['status']=='INFEASIBLE_ARC':
  domains={u:set(ms) for u,ms in result['initial'].items()}
  for event in result['events']:
   u,v=event['vertex'],event['against'];removed=set(event['removed']);assert removed<=domains[u]
   for a in removed:
    aa=g[u]|{w for w in U if a>>w&1}
    for b in domains[v]:
     bb=g[v]|{w for w in U if b>>w&1}
     assert ((v in aa)!=(u in bb)) or len(aa&bb)>1
   domains[u]-=removed
  assert not domains[result['empty_vertex']]

 assert check(adj,max_nodes=0)['status']=='UNKNOWN' and check(adj,deadline=time.monotonic()-1)['status']=='UNKNOWN'
 bad=[list(ns) for ns in adj];bad[0].append(0)
 try:check(bad);raise AssertionError('invalid accepted')
 except ValueError:pass
 summaries.append({'fixture':index,'rows':total,'generation_nodes':full['nodes'],'status':result['status'],'nodes':result['nodes']})
# Isolated compatibility/batch tests; these are synthetic domains, not research graphs.
g=[0]*49
ok=arc_consistency(g,{7:[1<<8],8:[1<<7]},Budget(100,None));assert ok['status']=='ARC_FEASIBLE'
bad=arc_consistency(g,{7:[1<<8],8:[0]},Budget(100,None));assert bad['status']=='INFEASIBLE_ARC'
batch=arc_consistency(g,{7:[1<<8,(1<<8)|(1<<9)],8:[0]},Budget(1,None));assert batch['status']=='UNKNOWN' and not batch['events'] and batch['remaining'][7]==[1<<8,(1<<8)|(1<<9)]
g[7]=1;g[8]=1
common=arc_consistency(g,{7:[1<<9],8:[1<<9]},Budget(100,None));assert common['status']=='INFEASIBLE_ARC'
(p/'receipts.json').write_text(json.dumps(receipts,indent=2)+'\n')
out={'status':'PASS','fixtures':summaries,'independent_full_row_sets':len(fixtures)*35,'template_bounds':{'4':210,'5':840},'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'synthetic_arc_cases':4,'seconds':time.monotonic()-start,'scope':'API and complete-domain tests on two already reviewed fixed empty-first partial graphs; no full incidence-class census or exclusion.'};(p/'results.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
