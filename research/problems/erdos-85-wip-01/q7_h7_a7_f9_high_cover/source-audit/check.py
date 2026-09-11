import pathlib,json,itertools,time
P=pathlib.Path(__file__).parent;S=P.parent/'h7-a7-noncycle-singleton-projection';cover=json.loads((S/'results.json').read_text());done=json.loads((S/'completion-results.json').read_text());bases=[];records={}
for r in done['results']:
 if r['F_index']!=9:continue
 assert r['status']=='COMPLETE'
 i=r['source_index'];rep=cover['representatives'][i];bases.append((dict(F_index=9,F_edges=rep['F_edges']),i,rep));records[9,i]=r
assert len(bases)==39
start=time.monotonic();out=[]
def bits(m):
 while m:
  b=m&-m;yield b.bit_length()-1;m-=b
for f,xi,x in bases:
 g=[0]*21
 def edge(u,v):g[u]|=1<<v;g[v]|=1<<u
 for u,v in f['F_edges']:edge(u,v)
 for u,hs in enumerate(x['singleton_hosts'],7):
  for e in hs:edge(u,e)
 target={u:5-g[u].bit_count() for u in range(7,21)};order=sorted(target,key=lambda u:(g[u].bit_count(),u));solutions=set();nodes=0
 def visit(k):
  global nodes
  nodes+=1
  if nodes>100000 or time.monotonic()-start>60:raise TimeoutError
  if k==14:
   assert all(g[u].bit_count()==target[u] for u in target) and all((g[u]&g[v]).bit_count()<=1 for u in range(21) for v in range(u))
   solutions.add(tuple((u,v) for u in range(7,21) for v in bits(g[u]) if v>u));return
  u=order[k];need=target[u]-g[u].bit_count()
  if need<0:return
  candidates=[v for v in order[k+1:] if g[v].bit_count()<target[v] and not(g[u]>>v&1) and all(not(g[v]&g[w]&~(1<<u)) for w in bits(g[u]))]
  for choice in itertools.combinations(candidates,need):
   if any(g[v]&g[w]&~(1<<u) for v,w in itertools.combinations(choice,2)):continue
   old=g[u]
   for v in choice:edge(u,v)
   visit(k+1)
   for v in choice:g[v]^=1<<u
   g[u]=old
 visit(0);r=records[f['F_index'],xi];assert r['status']=='COMPLETE' and solutions=={tuple(map(tuple,s)) for s in r['solutions']};out.append(dict(F_index=f['F_index'],X_index=xi,nodes=nodes,solutions=len(solutions)))
r=dict(status='PASS',cases=len(out),solutions=sum(x['solutions'] for x in out),nodes=sum(x['nodes'] for x in out),max_nodes=max(x['nodes'] for x in out),seconds=time.monotonic()-start,results=out);(P/'results.json').write_text(json.dumps(r,indent=2)+'\n');print({k:v for k,v in r.items() if k!='results'})
