import array, collections, gzip, hashlib, itertools, json, pathlib, sqlite3, sys, time
P=pathlib.Path('/tmp/erdos85-sol1-h7-a6-high-quotient')
A=pathlib.Path('/tmp/erdos85-sol1-h7-a6-projection-extension')
OUT=pathlib.Path(__file__).parent
start=time.monotonic()
def read(p): return json.loads(p.read_text())
def pins(p,root):
 for name,h in read(p).items(): assert hashlib.sha256((root/name).read_bytes()).hexdigest()==h, name
pins(P/'pins.json',P); pins(P/'source-pins.json',A)
db=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True);db.row_factory=sqlite3.Row
prem=dict(db.execute('select * from review_requests where id=2122').fetchone())
assert prem==read(P/'premise.json') and prem['status']=='resolved' and prem['resolution'].startswith('PASS')
cover=read(A/'source-cover-results.json'); comp=read(A/'source-completion-results.json')
layout=[]; colours=bytearray(); metadata=array.array('H')
with gzip.open(A/'high-colourings.jsonl.gz','rt') as f:
 for ri,line in enumerate(f):
  r=json.loads(line); assert r['status']=='COMPLETE'
  layout.append({k:r[k] for k in ['completion_index','singleton_index','F_index','X_index']}|dict(global_start=len(metadata),count=len(r['colourings'])))
  for c in r['colourings']:
   assert len(c)==11 and [c.count(h) for h in range(7)]==[1,1,1,2,2,2,2]
   assert [c.index(h) for h in range(3,7)]==sorted(c.index(h) for h in range(3,7))
   colours.extend(c); metadata.append(ri)
assert layout==read(P/'source-layout.json') and len(metadata)==818836
actions={int(k):v for k,v in read(P/'actions.json').items()}
def edge(es): return {tuple(sorted(e)) for e in es}
action_count=0
for ci,aa in actions.items():
 r=comp['results'][ci]; F=cover['cases'][r['F_index']]; X=F['representatives'][r['X_index']]
 fe,xe=edge(F['F_edges']),edge(X['X_edges']); hosts=X['singleton_hosts']
 expected=set()
 for ep in itertools.permutations(range(7)):
  if edge((ep[u],ep[v]) for u,v in fe)!=fe or edge((ep[u],ep[v]) for u,v in xe)!=xe: continue
  for cp in itertools.permutations(range(3)):
   if all(ep[hosts[11+k][0]]==hosts[11+cp[k]][0] for k in range(3)): expected.add((ep,cp))
 assert expected=={(tuple(a['E']),tuple(a['C'])) for a in aa} and len(expected)==len(aa)
 for a in aa:
  ep,dp,cp=a['E'],a['D'],a['C']; assert sorted(dp)==list(range(11))
  for d in range(11): assert {ep[e] for e in hosts[d]}==set(hosts[dp[d]])
  vp=ep+[7+d for d in dp]+[18+c for c in cp]
  assert sorted(a['solutions'])==list(range(len(r['solutions'])))
  for j,es in enumerate(r['solutions']): assert edge((vp[u],vp[v]) for u,v in es)==edge(r['solutions'][a['solutions'][j]])
  action_count+=1
 assert time.monotonic()-start<60
mapping=array.array('I');mapping.frombytes((P/'orbit-map.u32le').read_bytes())
if sys.byteorder!='little':mapping.byteswap()
assert len(mapping)==2*len(metadata)
counts=collections.Counter();used=collections.defaultdict(int)
for member in range(len(metadata)):
 rep,ai=mapping[2*member:2*member+2];assert rep<=member
 rm,mm=layout[metadata[rep]],layout[metadata[member]]
 ci=rm['completion_index']; assert mm['completion_index']==ci
 a=actions[ci][ai]; assert a['solutions'][rm['singleton_index']]==mm['singleton_index']
 # Infer the high-label bijection from actual target incidences, rather
 # than reproducing the author's canonical high-renaming algorithm.
 hp=list(a['C'])+[-1]*4
 for d in range(11):
  h=colours[11*rep+d]; target=colours[11*member+a['D'][d]]
  if hp[h]<0: hp[h]=target
  assert hp[h]==target
 assert sorted(hp)==list(range(7))
 counts[rep]+=1; used[rep]|=1<<ai
 if member%10000==0:assert time.monotonic()-start<60
reps=read(P/'representatives.json');assert set(counts)=={r['global_index'] for r in reps}
hist=collections.Counter();perF=collections.Counter()
for r in reps:
 g=r['global_index'];m=layout[metadata[g]];ci=m['completion_index']
 assert r['completion_index']==ci and r['singleton_index']==m['singleton_index']
 assert r['colouring_index']+m['global_start']==g
 assert counts[g]==r['orbit_size']==len(actions[ci])
 assert used[g]==(1<<len(actions[ci]))-1 and mapping[2*g]==g
 hist[r['orbit_size']]+=1;perF[m['F_index']]+=1
assert {str(k):v for k,v in hist.items()}==read(P/'results.json')['orbit_histogram']
assert len(reps)==425550 and sum(counts.values())==818836
assert time.monotonic()-start<60
result=dict(status='PASS',source_assignments=len(metadata),representatives=len(reps),actions=action_count,witnesses=sum(counts.values()),orbit_histogram=dict(hist),per_F_representatives=dict(perF),seconds=time.monotonic()-start)
(OUT/'results.json').write_text(json.dumps(result,indent=2)+'\n')
(OUT/'input-pins.json').write_text((P/'pins.json').read_text())
print(json.dumps(result))
