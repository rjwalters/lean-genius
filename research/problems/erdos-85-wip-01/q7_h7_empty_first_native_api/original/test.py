from pathlib import Path
import json,time,hashlib
import reference,native
p=Path(__file__).parent
fixtures=json.loads(Path('/tmp/erdos85-sol1-h7-empty-first-row-api/fixtures.json').read_text())+[r['adjacency'] for r in json.loads(Path('/tmp/erdos85-sol1-h7-empty-first-18base-pilot/input.json').read_text())]
assert len(fixtures)==20;(p/'fixtures.json').write_text(json.dumps(fixtures)+'\n')
comparisons=[];reference_seconds=native_seconds=0;expired=0
for i,g in enumerate(fixtures):
 t=time.monotonic();expected=reference.check(g);reference_seconds+=time.monotonic()-t
 t=time.monotonic();actual=native.check(g);native_seconds+=time.monotonic()-t;assert actual==expected,(i,'full')
 masks,support,E,U=reference.validate(g);b=reference.Budget(100000,None);reference.complete_domains(masks,support,U,b)
 caps=sorted(set([0,1,1000,5000,b.nodes,b.nodes+1,max(0,expected['nodes']-1),expected['nodes'],100000]))
 for cap in caps:
  a=reference.check(g,max_nodes=cap);z=native.check(g,max_nodes=cap);assert a==z,(i,cap,a['status'],z['status']);comparisons.append({'fixture':i,'budget':cap,'status':a['status'],'nodes':a['nodes']})
 a=reference.check(g,deadline=time.monotonic()-1);z=native.check(g,deadline=time.monotonic()-1);assert a==z and a['status']=='UNKNOWN';expired+=1
bad=[list(ns) for ns in fixtures[0]];bad[0].append(0)
for api in [reference,native]:
 for g,kw in [(bad,{}),(fixtures[0],{'max_nodes':-1}),(fixtures[0],{'max_nodes':0.5})]:
  try:api.check(g,**kw);raise AssertionError('invalid accepted')
  except ValueError:pass
out={'status':'PASS','fixtures':20,'full_object_budget_comparisons':len(comparisons),'expired_deadline_comparisons':expired,'invalid_cases_per_api':3,'reference_full_seconds':reference_seconds,'native_full_seconds':native_seconds,'comparisons':comparisons,'scope':'Only already checked fixed partial graphs for native API equivalence; no new colouring/domain search.'};(p/'results.json').write_text(json.dumps(out,indent=2)+'\n');print({k:v for k,v in out.items() if k!='comparisons'})
