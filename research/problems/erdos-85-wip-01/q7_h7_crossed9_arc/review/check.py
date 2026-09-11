import pathlib,json,gzip,hashlib,time,itertools
P=pathlib.Path('/tmp/erdos85-sol1-h7-crossed9-arc');O=pathlib.Path(__file__).parent
pins=json.loads((P/'pins.json').read_text());assert all(hashlib.sha256((P/f).read_bytes()).hexdigest()==h for f,h in pins.items())
source=json.loads((P/'profile-source.json').read_text());profile=next(r for r in source['results'] if not r['twins_adjacent'] and r['profile_index']==9)
data=json.loads(gzip.decompress((P/'results.json.gz').read_bytes()));assert profile['status']=='COMPLETE' and len(profile['assignments'])==1920
assert len(data['results'])==1920 and {r['assignment_index'] for r in data['results']}==set(range(1920))
seeddata=json.loads((P/'seed-source.json').read_text());seed=next(r for r in seeddata['patterns'] if not r['twins_adjacent']);names=seeddata['names'];ix={n:i for i,n in enumerate(names)};hosts=[ix[n] for n in ['S0a','S0b']+['P0'+str(c) for c in range(1,7)]]
def rebuild(index):
 g=list(map(set,seed['adjacency']))
 def edge(u,v):g[u].add(v);g[v].add(u)
 for h,mask in zip(hosts,profile['assignments'][index]):
  for j,(a,b) in enumerate(profile['edge_order']):
   if mask>>j&1:edge(h,ix['P'+str(a)+str(b)])
 for c in range(1,7):
  missing=[h for h in hosts if not g[h]&g[c]];assert len(missing)==2
  for h,t in zip(missing,'ab'):edge(h,ix['S'+str(c)+t])
 e=0
 for h in hosts:
  while len(g[h])<7:edge(h,ix['E'+str(e)]);e+=1
 assert e==7
 return [sorted(ns) for ns in g]
start=time.monotonic();summaries=[];allrows=events=failures=0

def bits(n):
 while n:
  b=n&-n;yield b.bit_length()-1;n-=b
for result in data['results']:
 idx=result['assignment_index'];assert rebuild(idx)==result['adjacency'];g=[sum(1<<v for v in ns) for ns in result['adjacency']];outside=[v for v in range(7,49) if not g[0]>>v&1];assert len(outside)==34 and result['status'] in ['INFEASIBLE_ARC','INFEASIBLE_LOCAL'];nodes=0
 local=result['status']=='INFEASIBLE_LOCAL'
 def tick():
  global nodes
  nodes+=1
  if nodes>100000 or time.monotonic()-start>60:raise TimeoutError
 try:
  domains={}
  for u in ([result['local_result']['vertex']] if local else outside):
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
   if local:assert not answers
   else:
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
  if not local:assert not domains[result['empty_vertex']]
  summaries.append({'source_index':idx,'status':'VERIFIED','generation_nodes':nodes})
 except TimeoutError:
  summaries.append({'source_index':idx,'status':'UNKNOWN','generation_nodes':nodes});break
assert all(hashlib.sha256((P/f).read_bytes()).hexdigest()==h for f,h in pins.items())
out={'results':summaries,'verified':sum(r['status']=='VERIFIED' for r in summaries),'unvisited':1920-len(summaries),'rows':allrows,'events':events,'failed_supports':failures,'nodes':sum(r['generation_nodes'] for r in summaries),'seconds':time.monotonic()-start,'pins':pins,'method':'Independent direct candidate-subset complete row enumeration, exact row-set comparison; sequential deletion replay using full final neighbour intersections. No author generator/filter imports.'}
(O/'results.json').write_text(json.dumps(out,indent=2)+'\n');print({k:v for k,v in out.items() if k not in ['results','pins']})
