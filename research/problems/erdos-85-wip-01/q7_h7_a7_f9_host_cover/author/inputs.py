"""Exact input adapter for accepted2121 F9 high pairings; no host search."""
import pathlib,json,itertools,hashlib,sqlite3
P=pathlib.Path(__file__).parent;S=P.parent/'h7-a7-noncycle-singleton-projection';H=P.parent/'h7-a7-f9-projection-extension';K=list(itertools.combinations(range(7),2))
def load():
 c=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True)
 for rid in [2116,2121]:
  r=c.execute('select status,resolution from review_requests where id=?',(rid,)).fetchone();assert r[0]=='resolved' and r[1].startswith('PASS')
 for root in [S,H]:
  for f,h in json.loads((root/'pins.json').read_text()).items():assert hashlib.sha256((root/f).read_bytes()).hexdigest()==h
 cover=json.loads((S/'results.json').read_text());done=json.loads((S/'completion-results.json').read_text());highs=json.loads((H/'high-results.json').read_text());edges={(r['source_index'],j):es for r in done['results'] if r['F_index']==9 and r['status']=='COMPLETE' for j,es in enumerate(r['solutions'])};assert len(edges)==1620
 assert highs['summary']['unvisited']==0 and all(r['status']=='COMPLETE' for r in highs['results']);return cover,edges,highs

def base_graph(cover,edges,r):
 key=(r['source_index'],r['singleton_index']);rep=cover['representatives'][key[0]];assert rep['F_index']==9
 g=[set() for _ in range(49)]
 def add(u,v):g[u].add(v);g[v].add(u)
 ren=lambda u:u+42 if u<7 else u
 for u,v in rep['F_edges']+edges[key]:add(ren(u),ren(v))
 for s,hosts in enumerate(rep['singleton_hosts'],7):
  for e in hosts:add(s,42+e)
 for p,(u,v) in enumerate(K,21):add(p,u);add(p,v)
 return g

def given_high(base,pairing):
 g=[set(ns) for ns in base]
 for h,d in enumerate(pairing):
  for s in [14+h,7+d]:g[h].add(s);g[s].add(h)
 return [sorted(ns) for ns in g]

if __name__=='__main__':
 import time
 start=time.monotonic();cover,edges,highs=load();checked=0;examples=[]
 for r in highs['results']:
  base=base_graph(cover,edges,r)
  for pi,p in enumerate(r['pairings']):
   adj=given_high(base,p);g=[sum(1<<v for v in ns) for ns in adj]
   assert all(len(adj[h])==8 for h in range(7)) and all(len(adj[v])==2 for v in range(21,42))
   assert all(len(adj[s]) in (4,5) for s in range(7,21))
   assert all(len(adj[e])==7-sum(v>=42 for v in adj[e]) for e in range(42,49))
   assert all((g[u]&g[v]).bit_count()<=1 for u in range(49) for v in range(u))
   if len(examples)<3:examples.append(dict(case_index=r['case_index'],pairing_index=pi,adjacency=adj))
   checked+=1
 assert checked==28336
 (P/'input-verification.json').write_text(json.dumps(dict(status='PASS',graphs=checked,seconds=time.monotonic()-start,scope='Input reconstruction only; no host assignments or exclusions.'))+'\n');(P/'input-fixtures.json').write_text(json.dumps(examples)+'\n');print(checked,'input graphs verified',time.monotonic()-start)
