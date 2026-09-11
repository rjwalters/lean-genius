from pathlib import Path
import json,hashlib,itertools,importlib.util,time,collections,copy
P=Path('/Users/rwalters/lean-genius-q7-outside-first-20260910/h7-singleton-complete-row-api');O=Path(__file__).parent
pins=json.loads((P/'pins.json').read_text())
for f,h in pins.items():assert hashlib.sha256((P/f).read_bytes()).hexdigest()==h
spec=importlib.util.spec_from_file_location('api',P/'filter.py');api=importlib.util.module_from_spec(spec);spec.loader.exec_module(api)
fixtures=json.loads((P/'fixtures.json').read_text());assert len(fixtures)==33
perm=list(range(7))+[7+(v-7+13)%42 for v in range(7,49)]
for old in [fixtures[0],fixtures[16]]:
 renamed=[[] for _ in range(49)]
 for u,ns in enumerate(old):renamed[perm[u]]=sorted(perm[v] for v in ns)
 fixtures.append(renamed)


def bits(n):
 while n:
  b=n&-n;yield b.bit_length()-1;n-=b
records=[];start=time.monotonic()
for graph in fixtures:
 g=[sum(1<<v for v in ns) for ns in graph];U=[u for u in range(7,49) if g[u]&127];sup=[m&127 for m in g];domains={};nodes=0
 def tick():
  global nodes
  nodes+=1
  if nodes>100000 or time.monotonic()-start>60:raise TimeoutError
 for u in U:
  missing=127
  for w in bits(g[u]):missing&=~sup[w]
  cands=[v for v in U if v!=u and not(g[u]>>v&1) and not(sup[u].bit_count()==sup[v].bit_count()==1) and all(not g[v]&g[w] for w in bits(g[u]))]
  compat=[sum(1<<j for j,w in enumerate(cands) if v!=w and not(g[v]&g[w])) for v in cands];answers=set()
  def visit(avail,need,left,row):
   tick()
   if not need:
    if not left:answers.add(row)
    return
   if avail.bit_count()<need:return
   while avail:
    b=avail&-avail;avail-=b;j=b.bit_length()-1;v=cands[j]
    if sup[v]&~left:continue
    visit(avail&compat[j],need-1,left^sup[v],row|(1<<v))
  visit((1<<len(cands))-1,7-len(graph[u]),missing,0);domains[u]=answers
 bg=api.Budget(100000,time.monotonic()+60);actual=api.complete_domains(g,sup,U,bg);assert actual['status']=='DOMAINS_COMPLETE'
 assert set(actual['initial'])==set(domains)
 for u in U:assert len(actual['initial'][u])==len(set(actual['initial'][u])) and set(actual['initial'][u])==domains[u]
 result=api.check(graph,max_nodes=100000,deadline=time.monotonic()+60)
 for u,rows in result['initial'].items():assert set(rows)==domains[u]
 ds={u:set(v) for u,v in domains.items()};removed_count=0
 for e in result.get('events',[]):
  u,v=e['vertex'],e['against'];assert u!=v
  bad=set(e['removed']);assert len(bad)==len(e['removed']) and bad<=ds[u]
  for a in bad:
   assert all(((a>>v)&1)!=((b>>u)&1) or ((g[u]|a)&(g[v]|b)).bit_count()>1 for b in ds[v])
  ds[u]-=bad;removed_count+=len(bad)
 if result['status'] in ['INFEASIBLE_ROW','INFEASIBLE_ARC']:assert not ds[result['empty_vertex']]
 else:assert {u:set(v) for u,v in result['remaining'].items()}==ds
 for cap,deadline in [(0,None),(100000,time.monotonic()-1)]:
  guard=api.check(graph,max_nodes=cap,deadline=deadline);assert guard['status']=='UNKNOWN' and guard['stage']=='generation' and guard['initial']=={}
 records.append({'row_domains':len(domains),'rows':sum(map(len,domains.values())),'independent_nodes':nodes,'api_nodes':result['nodes'],'status':result['status'],'deleted_rows_checked':removed_count})
# Internal arc cutoff: unsupported row must not be removed before a whole batch finishes.
g=[0]*49;initial={7:[1<<8,0],8:[0,1<<7]};budget=api.Budget(0,None)
r=api.arc_consistency(g,initial,budget);assert r['status']=='UNKNOWN' and r['events']==[] and r['remaining']==initial
bad=copy.deepcopy(fixtures[0]);bad[0].append(0)
try:api.check(bad)
except ValueError:pass
else:raise AssertionError('invalid selfloop accepted')
for f,h in pins.items():assert hashlib.sha256((P/f).read_bytes()).hexdigest()==h
r={'status':'PASS','fixtures':records,'complete_row_domains':sum(x['row_domains'] for x in records),'rows':sum(x['rows'] for x in records),'guard_checks':2*len(fixtures),'invalid_selfloop_rejected':True,'unfinished_arc_batch_preserved':True,'seconds':time.monotonic()-start,'pins':pins,'scope':'Independent increasing-subset rows on35S-complete fixture partials, unlike author least-colour traversal; exact complete-domain equality and returned trace replay. No whole incidence-family or H7 exclusion.'}
(O/'results.json').write_text(json.dumps(r,indent=2)+'\n');(O/'fixtures.json').write_text(json.dumps(fixtures)+'\n');print({k:v for k,v in r.items() if k!='pins'})
