import pathlib,json,time,sqlite3,hashlib,collections
P=pathlib.Path(__file__).parent;S=P.parent/'h7-a7-noncycle-singleton-projection';assert not (P/'high-results.json').exists()
c=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True);c.row_factory=sqlite3.Row;r=dict(c.execute('select * from review_requests where id=2116').fetchone());assert r['status']=='resolved' and r['resolution'].startswith('PASS')
for f,h in json.loads((S/'pins.json').read_text()).items():assert hashlib.sha256((S/f).read_bytes()).hexdigest()==h
cover=json.loads((S/'results.json').read_text());done=json.loads((S/'completion-results.json').read_text());records=[r for r in done['results'] if r['F_index']==9];assert len(records)==39 and all(r['status']=='COMPLETE' for r in records);cases=[(r['source_index'],j,es) for r in records for j,es in enumerate(r['solutions'])];assert len(cases)==1620
start=time.monotonic();deadline=start+60;out=[]
for index,(si,sj,es) in enumerate(cases):
 if time.monotonic()>deadline:break
 rep=cover['representatives'][si];g=[0]*21
 def edge(u,v):g[u]|=1<<v;g[v]|=1<<u
 for u,v in rep['F_edges']+es:edge(u,v)
 for s,hs in enumerate(rep['singleton_hosts'],7):
  for e in hs:edge(s,e)
 allowed=[[d for d in range(7) if not(g[14+h]>>(7+d)&1) and not(g[14+h]&g[7+d])] for h in range(7)];order=sorted(range(7),key=lambda h:(len(allowed[h]),h));pair=[-1]*7;solutions=[];nodes=0
 def visit(k,used):
  global nodes
  nodes+=1
  if nodes>100000 or time.monotonic()>deadline:raise TimeoutError
  if k==7:solutions.append(list(pair));return
  h=order[k]
  for d in allowed[h]:
   if not used>>d&1:pair[h]=d;visit(k+1,used|1<<d)
 try:visit(0,0);status='COMPLETE'
 except TimeoutError:status='UNKNOWN'
 out.append(dict(case_index=index,source_index=si,singleton_index=sj,status=status,nodes=nodes,allowed=allowed,pairings=solutions))
summary=dict(total=len(cases),visited=len(out),unvisited=len(cases)-len(out),counts=dict(collections.Counter(r['status'] for r in out)),positive=sum(bool(r['pairings']) for r in out),pairings=sum(len(r['pairings']) for r in out),nodes=sum(r['nodes'] for r in out),max_nodes=max(r['nodes'] for r in out),seconds=time.monotonic()-start)
(P/'high-results.json').write_text(json.dumps(dict(summary=summary,results=out),separators=(',',':'))+'\n');print(summary)
