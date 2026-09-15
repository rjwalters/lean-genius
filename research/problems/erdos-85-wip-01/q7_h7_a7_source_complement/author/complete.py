"""One exact unfinished source slice; the reviewed traversal is unchanged."""
import pathlib,json,itertools,math,time,collections,hashlib,sqlite3
P=pathlib.Path(__file__).parent
S=pathlib.Path('/Users/rwalters/GitHub/lean-genius/.codex/worktrees/erdos85-sol2-integration/research/problems/erdos-85-wip-01/q7_h7_a7_noncycle_singleton_projection/author')
assert not (P/'launch.json').exists(),'No overwrite or restart'
source=json.loads((S/'results.json').read_text());prior=json.loads((S/'completion-results.json').read_text())
source_pins={n:hashlib.sha256((S/n).read_bytes()).hexdigest() for n in ['results.json','completion-results.json','complete.py']}
assert source_pins['results.json']=='65f4a201de9352823202e6a3466b97fd444c76cbc9c399f8395b71244c8a25d4'
assert source_pins['completion-results.json']=='d338a26809f2553d7889fb702f8947046ef83a80ae14fd766e93ee1496c1f64f'
db=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True)
review=db.execute('select status,resolution from review_requests where id=2116').fetchone();assert review[0]=='resolved' and review[1].startswith('PASS')
known={r['source_index'] for r in prior['results'] if r['status']=='COMPLETE'}
assert known==set(range(860)) and len(source['representatives'])==1310
queue=[i for i in range(1310) if i not in known];assert queue==list(range(860,1310))
assert [(r['source_index'],r['nodes']) for r in prior['results'] if r['status']=='UNKNOWN']==[(860,55627)]
(P/'queue.json').write_text(json.dumps(queue)+'\n')
with (P/'launch.json').open('x') as f:json.dump({'source':str(S),'source_pins':source_pins,'source_review':2116,'inherited_complete':860,'new_queue':450,'aggregate_seconds':120,'max_nodes':100000,'artifact_byte_cap':100000000,'driver_sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest()},f,indent=2)
def bits(mask):
 while mask:
  bit=mask&-mask;yield bit.bit_length()-1;mask-=bit
out=[];size=0;stop=None;unsaved=0;start=time.monotonic();deadline=start+120
for index in queue:
 if time.monotonic()>deadline:stop='AGGREGATE_CAP';break
 r=source['representatives'][index]
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
 row=dict(source_index=index,F_index=r['F_index'],status=status,nodes=nodes,solutions=sorted(solutions),count=len(solutions))
 encoded=json.dumps(row,separators=(',',':'))
 if size+len(encoded.encode())>99000000:stop='ARTIFACT_CAP';unsaved=1;break
 size+=len(encoded.encode());out.append(row)
summary=dict(total=len(queue),visited=len(out),unvisited=len(queue)-len(out),counts=dict(collections.Counter(r['status'] for r in out)),positive=sum(r['count']>0 for r in out),solutions=sum(r['count'] for r in out),max_nodes=max([r['nodes'] for r in out],default=0),seconds=time.monotonic()-start,stop=stop,computed_not_saved=unsaved,inherited_complete=860)
raw=json.dumps(dict(summary=summary,results=out),separators=(',',':'))+'\n';assert len(raw.encode())<100000000
(P/'completion-results.json').write_text(raw)
print(json.dumps(summary))
