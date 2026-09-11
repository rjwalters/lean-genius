from pathlib import Path
import json,hashlib,sqlite3,gzip,functools,time,itertools
P=Path('/tmp/erdos85-sol1-h7-a6-projection-extension');O=Path(__file__).parent;S=O.parent/'h7-a6-empty-singleton-projection';A=Path('/tmp/erdos85-sol1-h7-a6-high-api');start=time.monotonic()
for f,h in json.loads((P/'pins.json').read_text()).items():assert hashlib.sha256((P/f).read_bytes()).hexdigest()==h
for f in ['cover-results.json','completion-results.json','pins.json']:assert (P/('source-'+f)).read_bytes()==(S/f).read_bytes()
for f in ['high.cpp','high.dylib','CRITERION.md']:assert (P/f).read_bytes()==(A/f).read_bytes()
c=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True);c.row_factory=sqlite3.Row
for old in json.loads((P/'high-premises.json').read_text()):
 live=dict(c.execute('select * from review_requests where id=?',(old['id'],)).fetchone());assert live==old and live['status']=='resolved' and live['resolution'].startswith('PASS')
cover=json.loads((P/'source-cover-results.json').read_text());comp=json.loads((P/'source-completion-results.json').read_text());summary=json.loads((P/'high-results.json').read_text());expected=[(i,j) for i,r in enumerate(comp['results']) for j in range(len(r['solutions']))];assert len(expected)==3284
seen=[];total=states=maxstates=direct=0;maxnodes=0
with gzip.open(P/'high-colourings.jsonl.gz','rt') as stream:
 for line in stream:
  item=json.loads(line);i,j=item['completion_index'],item['singleton_index'];seen.append((i,j));assert item['status']=='COMPLETE' and item['nodes']<=100000;maxnodes=max(maxnodes,item['nodes'])
  r=comp['results'][i];F=cover['cases'][r['F_index']];X=F['representatives'][r['X_index']];assert item['F_index']==r['F_index'] and item['X_index']==r['X_index'];g=[0]*28
  def edge(g,u,v):g[u]|=1<<v;g[v]|=1<<u
  for u,v in F['F_edges']+r['solutions'][j]:edge(g,u,v)
  for u,hs in enumerate(X['singleton_hosts'],7):
   for v in hs:edge(g,u,v)
  # One perfect matching on all14 singleton vertices, allowing leaf/core and leaf/leaf.
  compat=[0]*14
  for a,b in itertools.combinations(range(14),2):
   if a>=11:continue
   if g[7+a]&g[7+b]:continue
   if b>=11 and g[7+a]>>(7+b)&1:continue
   compat[a]|=1<<b;compat[b]|=1<<a
  @functools.lru_cache(None)
  def count(mask):
   if not mask:return 1
   bit=mask&-mask;a=bit.bit_length()-1;rest=mask^bit;opts=rest&compat[a];n=0
   while opts:
    b=opts&-opts;opts-=b;n+=count(rest^b)
   return n
  n=count((1<<14)-1);local=count.cache_info().currsize;assert local<=100000 and time.monotonic()-start<60
  states+=local;maxstates=max(maxstates,local)
  codes=set(map(tuple,item['colourings']));assert len(codes)==len(item['colourings'])==n and n>0
  for ci,code in enumerate(codes):
   assert len(code)==11 and all(0<=h<7 for h in code)
   groups=[[d for d in range(11) if code[d]==h] for h in range(7)]
   assert list(map(len,groups))==[1,1,1,2,2,2,2]
   assert [ds[0] for ds in groups[3:]]==sorted(ds[0] for ds in groups[3:])
   ps=[(groups[h][0],11+h) for h in range(3)]+[tuple(ds) for ds in groups[3:]]
   assert all(compat[a]>>b&1 for a,b in ps)
   if ci==0:
    ng=g[:]
    for h,(a,b) in enumerate(ps):edge(ng,21+h,7+a);edge(ng,21+h,7+b)
    assert all((ng[a]&ng[b]).bit_count()<=1 for a in range(28) for b in range(a));direct+=1
  total+=n
assert seen==expected and total==818836 and summary['visited']==3284 and summary['complete']==3284 and summary['unvisited']==summary['unknown']==summary['empty']==0 and not summary['artifact_stop']
out=dict(status='PASS',cases=len(seen),colourings=total,matching_DP_states=states,max_DP_states=maxstates,max_author_nodes=maxnodes,direct_graph_fixtures=direct,seconds=time.monotonic()-start,scope='Exact2118 source bytes and ordered3284case join; independent whole14vertex perfect-matching DP interleaves mixed/double pair choices. Count plus validity/canonical uniqueness proves every818836assignment. One direct28vertex high-graph C4 check per case. No P-host stage or full graph closure.')
(O/'results.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
