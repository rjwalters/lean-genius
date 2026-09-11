from pathlib import Path
import json,hashlib,time
P=Path('/tmp/erdos85-sol1-h7-empty-first-18base-pilot');O=Path(__file__).parent;sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();pins=json.loads((P/'pins.json').read_text())
for f,h in pins.items():assert sha(P/f)==h
assert sha(P/'filter.py')==sha(Path('/tmp/erdos85-sol1-h7-empty-first-row-api/filter.py'))
assert sha(P/'input.json')==sha(Path('/Users/rwalters/lean-genius-q7-outside-first-20260910/h7-a7-empty-first-singleton-rows/surviving-bases.json'))
inputs=json.loads((P/'input.json').read_text());data=json.loads((P/'results.json').read_text());receipts=data['results'];assert len(inputs)==len(receipts)==18
assert [r['source_index'] for r in inputs]==[r['source_index'] for r in receipts] and len({r['source_index'] for r in inputs})==18
start=time.monotonic();allrows=events=failures=allnodes=0

def bits(n):
 while n:
  b=n&-n;yield b.bit_length()-1;n-=b
for inp,result in zip(inputs,receipts):
 graph=inp['adjacency'];g=[sum(1<<v for v in ns) for ns in graph];U=[u for u in range(7,49) if g[u]&127];sup=[m&127 for m in g];domains={};nodes=0
 assert all((g[u]&g[v]).bit_count()<=1 for u in range(49) for v in range(u))
 def tick():
  global nodes
  nodes+=1
  if nodes>100000 or time.monotonic()-start>60:raise TimeoutError
 for u in U:
  cands=[v for v in U if v!=u and all(not g[v]&g[w] for w in bits(g[u]))]
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
  visit((1<<len(cands))-1,7-len(graph[u]),127,0);domains[u]=answers
  assert set(result['initial'][str(u)])==answers and len(result['initial'][str(u)])==len(answers);allrows+=len(answers)
 assert {int(k) for k in result['initial']}==set(domains)
 for event in result.get('events',[]):
  u,v=event['vertex'],event['against'];assert u!=v
  bad=set(event['removed']);assert len(bad)==len(event['removed']) and bad<=domains[u]
  for a in bad:
   for b in domains[v]:
    assert ((a>>v)&1)!=((b>>u)&1) or ((g[u]|a)&(g[v]|b)).bit_count()>1;failures+=1
  domains[u]-=bad;events+=1
 assert result['status'] in ['INFEASIBLE_ROW','INFEASIBLE_ARC'] and not domains[result['empty_vertex']];allnodes+=nodes
for f,h in pins.items():assert sha(P/f)==h
r={'status':'PASS','verified':18,'complete_domains':630,'rows':allrows,'events':events,'failed_supports':failures,'independent_nodes':allnodes,'seconds':time.monotonic()-start,'pins':pins,'scope':'Exact18exportedfixedbase endpoints, independent increasing-subset complete domains and full-neighbour deletion replay. No wholecolouringclass/H7/global exclusion.'};(O/'results.json').write_text(json.dumps(r,indent=2)+'\n');print({k:v for k,v in r.items() if k!='pins'})
