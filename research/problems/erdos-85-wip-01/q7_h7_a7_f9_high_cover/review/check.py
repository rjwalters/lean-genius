from pathlib import Path
import json,hashlib,sqlite3,itertools,time,functools
P=Path('/Users/rwalters/lean-genius-q7-outside-first-20260910/h7-a7-f9-projection-extension');S=P.parent/'h7-a7-noncycle-singleton-projection';O=Path(__file__).parent;start=time.monotonic()
for f,h in json.loads((P/'pins.json').read_text()).items():assert hashlib.sha256((P/f).read_bytes()).hexdigest()==h
for f,h in json.loads((P/'input-pins.json').read_text()).items():assert hashlib.sha256(Path(f).read_bytes()).hexdigest()==h
c=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True);c.row_factory=sqlite3.Row
for old in json.loads((P/'premises.json').read_text()):
 live=dict(c.execute('select * from review_requests where id=?',(old['id'],)).fetchone());live['refs']=json.loads(live['refs']);old.pop('expired',None);assert live==old and live['status']=='resolved' and live['resolution'].startswith('PASS')
cover=json.loads((S/'results.json').read_text());done=json.loads((S/'completion-results.json').read_text());data=json.loads((P/'high-results.json').read_text());indices=[i for i,r in enumerate(cover['representatives']) if r['F_index']==9];assert len(indices)==39
records={r['source_index']:r for r in done['results']};assert all(records[i]['status']=='COMPLETE' for i in indices)
expected=[(i,j,es) for i in indices for j,es in enumerate(records[i]['solutions'])];assert len(expected)==len(data['results'])==1620
count=positive=states=0
for ci,((i,j,es),r) in enumerate(zip(expected,data['results'])):
 assert (r['case_index'],r['source_index'],r['singleton_index'])==(ci,i,j) and r['status']=='COMPLETE' and r['nodes']<=100000
 rep=cover['representatives'][i];g=[0]*28
 def edge(g,u,v):g[u]|=1<<v;g[v]|=1<<u
 for u,v in rep['F_edges']+es:edge(g,u,v)
 for u,hs in enumerate(rep['singleton_hosts'],7):
  for v in hs:edge(g,u,v)
 allowed=[]
 for h in range(7):
  row=[]
  for d in range(7):
   u,v=14+h,7+d
   if g[u]>>v&1:continue
   ng=g[:];edge(ng,u,21+h);edge(ng,v,21+h)
   if all((ng[a]&ng[b]).bit_count()<=1 for a in range(28) for b in range(a)):row.append(d)
  allowed.append(row)
 assert allowed==r['allowed']
 # Reverse-core permanent DP: disjoint allowed bijections, exact count.
 @functools.lru_cache(None)
 def permanent(h,used):
  if h<0:return 1
  return sum(permanent(h-1,used|(1<<d)) for d in allowed[h] if not used>>d&1)
 n=permanent(6,0);states+=permanent.cache_info().currsize
 saved=set(map(tuple,r['pairings']));assert len(saved)==len(r['pairings'])==n
 for p in saved:
  assert sorted(p)==list(range(7)) and all(d in allowed[h] for h,d in enumerate(p))
  ng=g[:]
  for h,d in enumerate(p):edge(ng,21+h,14+h);edge(ng,21+h,7+d)
  assert all((ng[a]&ng[b]).bit_count()<=1 for a in range(28) for b in range(a))
 count+=n;positive+=bool(n)
assert count==28336 and positive==1472
summary=data['summary'];assert summary['total']==1620 and summary['visited']==1620 and summary['unvisited']==0 and summary['counts']=={'COMPLETE':1620} and summary['pairings']==count
out=dict(status='PASS',F_host_classes=39,S_graphs=1620,pairings=count,positive=positive,negative=1620-positive,permanent_states=states,seconds=time.monotonic()-start,scope='Exact full F9 source restriction to COMPLETE E/S records. Independent direct28vertex high insertion derives every allowed pair; reverse-core permanent count plus distinct membership proves exact saved sets. Every28336 fully high-coloured graph directly C4 checked. No P-host stage or old capped base repeated.')
(O/'results.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
