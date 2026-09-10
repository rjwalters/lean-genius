import pathlib,json,gzip,hashlib,time,itertools
P=pathlib.Path('/Users/rwalters/lean-genius-q7-outside-first-20260910/h7-crossed10-arc');O=pathlib.Path(__file__).parent
pins=json.loads((P/'pins.json').read_text());assert all(hashlib.sha256((P/f).read_bytes()).hexdigest()==h for f,h in pins.items())
data=json.loads(gzip.decompress((P/'results.json.gz').read_bytes()));assert [r['assignment_index'] for r in data['results']]==list(range(1647));assert sum(r['status']=='INFEASIBLE_LOCAL' for r in data['results'])==95;assert sum(r['status']=='INFEASIBLE_ARC' for r in data['results'])==1552
start=time.monotonic();summaries=[];allrows=events=failures=0

def bits(n):
 while n:
  b=n&-n;yield b.bit_length()-1;n-=b
for result in data['results']:
 idx=result['assignment_index'];g=[sum(1<<v for v in ns) for ns in result['adjacency']];outside=[v for v in range(7,49) if not g[0]>>v&1];assert len(outside)==34;nodes=0
 def tick():
  global nodes
  nodes+=1
  if nodes>100000 or time.monotonic()-start>60:raise TimeoutError
 try:
  domains={}
  vertices=outside if result['status']=='INFEASIBLE_ARC' else [result['local_result']['vertex']]
  for u in vertices:
   missing=127
   for v in bits(g[u]):missing&=~(g[v]&127)
   candidates=[v for v in outside if v!=u and (g[v]&127)&~missing==0 and all(not(g[v]&g[w]) for w in bits(g[u]))]
   masks=[g[v]&127 for v in candidates];compat=[sum(1<<j for j,w in enumerate(candidates) if v!=w and not(g[v]&g[w])) for v in candidates];answers=set()
   # Direct increasing-subset traversal, no host grouping or skip/group generator.
   def dfs(avail,need,left,row):
    tick()
    if need==0:
     if left==0:answers.add(row)
     return
    if avail.bit_count()<need:return
    possible=0
    for j in bits(avail):possible|=masks[j]
    if left&~possible:return
    while avail:
     bit=avail&-avail;avail-=bit;j=bit.bit_length()-1
     if masks[j]&~left:continue
     dfs(avail&compat[j],need-1,left^masks[j],row|(1<<candidates[j]))
   dfs((1<<len(candidates))-1,7-g[u].bit_count(),missing,0)
   if result['status']=='INFEASIBLE_LOCAL':
    assert not answers,(idx,u,'local negative has legal row')
    continue
   assert len(result['initial'][str(u)])==len(set(result['initial'][str(u)]))
   assert answers==set(result['initial'][str(u)]),(idx,u,len(answers),len(result['initial'][str(u)]))
   domains[u]=answers;allrows+=len(answers)
  for event in result.get('events',[]):
   u,v=event['vertex'],event['against'];assert u!=v
   removed=set(event['removed']);assert len(removed)==len(event['removed']) and removed<=domains[u]
   for a in removed:
    for b in domains[v]:
     # Compare full final neighbour sets, not the author's old/new split.
     assert ((a>>v)&1)!=((b>>u)&1) or ((g[u]|a)&(g[v]|b)).bit_count()>1
     failures+=1
   domains[u]-=removed;events+=1
  if result['status']=='INFEASIBLE_ARC':assert not domains[result['empty_vertex']]
  summaries.append({'source_index':idx,'status':'VERIFIED','generation_nodes':nodes})
 except TimeoutError:
  summaries.append({'source_index':idx,'status':'UNKNOWN','generation_nodes':nodes});break
assert all(hashlib.sha256((P/f).read_bytes()).hexdigest()==h for f,h in pins.items())
out={'results':summaries,'verified':sum(r['status']=='VERIFIED' for r in summaries),'unvisited':1647-len(summaries),'rows':allrows,'events':events,'failed_supports':failures,'nodes':sum(r['generation_nodes'] for r in summaries),'seconds':time.monotonic()-start,'pins':pins,'method':'Independent direct candidate-subset complete row enumeration, exact row-set comparison; sequential deletion replay using full final neighbour intersections. No author generator/filter imports.'}
(O/'results.json').write_text(json.dumps(out,indent=2)+'\n');print({k:v for k,v in out.items() if k not in ['results','pins']})
