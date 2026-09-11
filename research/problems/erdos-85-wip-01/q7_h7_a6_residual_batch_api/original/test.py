import json,pathlib,time
import api,reference
P=pathlib.Path(__file__).parent;count=guards=0
fixtures=json.loads((P/'fixtures.json').read_text())
for adj in fixtures:
 g,support,E,U=reference.validate(adj);PV=[p for p in U if support[p].bit_count()==2];fixed=[sum(1<<p for p in PV if g[e]>>p&1) for e in E]
 base=[set(ns) for ns in adj]
 for e in E:
  for p in PV:base[e].discard(p);base[p].discard(e)
 complete=reference.check(adj)
 for cap in sorted({0,1,2,complete['nodes']//2,complete['nodes']-1,complete['nodes'],100000}):
  expected=reference.check(adj,max_nodes=cap)
  if expected['status']=='INFEASIBLE_ROW':expected={k:expected[k] for k in ['status','empty_vertex','nodes']}
  assert api.check_hosts(base,E,[fixed],max_nodes=cap)==[expected];count+=1
 assert api.check_hosts(base,E,[fixed],deadline=time.monotonic()-1)==[];guards+=1
 assert len(api.check_hosts(base,E,[fixed,fixed],max_nodes=0))==2;guards+=1
 assert api.check_hosts(base,E,[])==[];guards+=1
 for empties,ms in [(E[:6]+[E[0]],fixed),(E,[1]+fixed[1:])]:
  try:api.check_hosts(base,empties,[ms]);raise AssertionError('invalid accepted')
  except ValueError:guards+=1
 bad=[set(ns) for ns in base];bad[0].add(0)
 try:api.check_hosts(bad,E,[fixed]);raise AssertionError('selfloop accepted')
 except ValueError:guards+=1
out=dict(status='PASS',fixtures=len(fixtures),comparisons=count,guards=guards)
(P/'test-results.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
