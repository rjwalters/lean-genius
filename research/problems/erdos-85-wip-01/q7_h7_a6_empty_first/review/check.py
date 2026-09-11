import pathlib,json,itertools,hashlib,sqlite3,time
P=pathlib.Path(__file__).parent;A=pathlib.Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3/h7-a6-empty-first');read=lambda p:json.loads(p.read_text());pins=read(A/'pins.json')
for f,h in pins.items():assert hashlib.sha256((A/f).read_bytes()).hexdigest()==h
c=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True);c.row_factory=sqlite3.Row
for old in read(A/'premises.json'):
 live=dict(c.execute('select * from review_requests where id=?',(old['id'],)).fetchone());live['refs']=json.loads(live['refs']);old.pop('expired',None);assert old==live and live['resolution'].startswith('PASS')
K=list(itertools.combinations(range(7),2));out=[];start=time.monotonic()
for f in read(A/'results.json')['fixtures']:
 R=set(map(tuple,f['R_edges']));F=set(map(tuple,f['F_edges']));phi={tuple(e):x for e,x in f['phi']};assert set(phi)==set(K)-R
 fg=[set() for _ in range(7)]
 for x,y in F:fg[x].add(y);fg[y].add(x)
 for x in range(7):
  es=[e for e,c in phi.items() if c==x];assert len(es)==len(fg[x]) and len(set(sum((list(e) for e in es),[])))==2*len(es)
 rows=[]
 for i in range(7):
  U=set(range(7))-{x for e,x in phi.items() if i in e};opts=set()
  for perm in itertools.permutations(U):
   blocks=(tuple(sorted(perm[:2])),tuple(sorted(perm[2:])))
   if len(U)==4:blocks=tuple(sorted(blocks))
   opts.add(blocks)
  assert len(opts)==3 and opts==set(tuple(map(tuple,r)) for r in f['choices'][i]);rows.append(sorted(opts))
 good=0;tested=0
 for choices in itertools.product(*rows):
  tested+=1;adj=[set() for _ in range(49)]
  # Independent numbering: E0..6, pairs7..27, S28..41, H42..48.
  def edge(u,v):adj[u].add(v);adj[v].add(u)
  for x,y in F:edge(x,y)
  for k,e in enumerate(K):
   for i in e:edge(7+k,42+i)
   if e in phi:edge(7+k,phi[e])
  for i,blocks in enumerate(choices):
   for j,block in enumerate(blocks):
    s=28+2*i+j;edge(s,42+i)
    for x in block:edge(s,x)
  assert all(len(adj[x])==7 for x in range(7)) and all(len(adj[x])==8 for x in range(42,49))
  assert all(len(adj[x]&adj[h])==1 for x in range(7) for h in range(42,49))
  seen=set();actual=True
  for neighbors in adj:
   for ends in itertools.combinations(sorted(neighbors),2):
    if ends in seen:actual=False;break
    seen.add(ends)
   if not actual:break
  pairs=[b for row in choices for b in row if len(b)==2]
  predicted=len(set(pairs))==11 and all(not fg[x]&fg[y] for x,y in pairs)
  assert predicted==actual
  good+=actual
 assert tested==2187 and good==f['c4_free_choices'];out.append(dict(tested=tested,good=good))
r=dict(status='PASS',fixtures=out,pins=len(pins),seconds=time.monotonic()-start);(P/'results.json').write_text(json.dumps(r,indent=2)+'\n');print(r)
