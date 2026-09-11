import pathlib,json,itertools,math,time,collections
P=pathlib.Path(__file__).parent;assert not (P/'completion-results.json').exists();source=json.loads((P/'results.json').read_text());out=[];start=time.monotonic();deadline=start+60

def bits(mask):
 while mask:
  bit=mask&-mask;yield bit.bit_length()-1;mask-=bit
for index,r in enumerate(source['representatives']):
 if time.monotonic()>deadline:break
 base=[0]*21
 def edge(g,u,v):g[u]|=1<<v;g[v]|=1<<u
 for u,v in r['F_edges']:edge(base,u,v)
 for u,hs in enumerate(r['singleton_hosts'],7):
  for e in hs:edge(base,u,e)
 target={u:5-base[u].bit_count() for u in range(7,21)};g=base[:];solutions=set();nodes=0
 def visit(unfixed):
  global nodes
  nodes+=1
  if nodes>100000 or time.monotonic()>deadline:raise TimeoutError
  if not unfixed:
   assert all(g[u].bit_count()==target[u] for u in target) and all((g[u]&g[v]).bit_count()<=1 for u in range(21) for v in range(u))
   solutions.add(tuple((u,v) for u in range(7,21) for v in bits(g[u]) if v>u));return
  choices=[]
  for u in unfixed:
   need=target[u]-g[u].bit_count()
   if need<0:return
   candidates=[v for v in unfixed if v!=u and target[v]>g[v].bit_count() and not(g[u]>>v&1) and all(not(g[v]&g[w]) for w in bits(g[u]))]
   if need>len(candidates):return
   choices.append((math.comb(len(candidates),need),u,need,candidates))
  _,u,need,candidates=min(choices,key=lambda x:(x[0],-x[1]))
  for block in itertools.combinations(candidates,need):
   if any(g[v]&g[w] for v,w in itertools.combinations(block,2)):continue
   old=g[u]
   for v in block:edge(g,u,v)
   visit(tuple(v for v in unfixed if v!=u))
   for v in block:g[v]^=1<<u
   g[u]=old
 try:visit(tuple(range(7,21)));status='COMPLETE'
 except TimeoutError:status='UNKNOWN'
 out.append(dict(source_index=index,F_index=r['F_index'],status=status,nodes=nodes,solutions=sorted(solutions),count=len(solutions)))
summary=dict(total=len(source['representatives']),visited=len(out),unvisited=len(source['representatives'])-len(out),counts=dict(collections.Counter(r['status'] for r in out)),positive=sum(r['count']>0 for r in out),solutions=sum(r['count'] for r in out),max_nodes=max(r['nodes'] for r in out),seconds=time.monotonic()-start)
raw=json.dumps(dict(summary=summary,results=out),separators=(',',':'))+'\n';assert len(raw.encode())<100000000;(P/'completion-results.json').write_text(raw);print(summary)
