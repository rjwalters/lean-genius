import array,collections,gzip,hashlib,itertools,json,pathlib,sys,time
P=pathlib.Path(__file__).parent;A=pathlib.Path('/tmp/erdos85-sol1-h7-a6-projection-extension')
for f,h in json.loads((P/'source-pins.json').read_text()).items():assert hashlib.sha256((A/f).read_bytes()).hexdigest()==h
cover=json.loads((A/'source-cover-results.json').read_text());comp=json.loads((A/'source-completion-results.json').read_text());layout=json.loads((P/'source-layout.json').read_text())
colours=[];meta=[];actual_layout=[]
with gzip.open(A/'high-colourings.jsonl.gz','rt') as stream:
 for line in stream:
  r=json.loads(line);assert r['status']=='COMPLETE';ci,j=r['completion_index'],r['singleton_index'];n=len(r['colourings'])
  actual_layout.append({k:r[k] for k in ['completion_index','singleton_index','F_index','X_index']}|dict(global_start=len(colours),count=n))
  colours.extend(r['colourings']);meta.extend([(ci,j)]*n)
assert actual_layout==layout and len(colours)==818836
actions={int(k):v for k,v in json.loads((P/'actions.json').read_text()).items()};reps=json.loads((P/'representatives.json').read_text());mapping=array.array('I');mapping.frombytes((P/'orbit-map.u32le').read_bytes())
if sys.byteorder!='little':mapping.byteswap()
assert len(mapping)==2*len(colours)
start=time.monotonic();perms={};edge_cache={};action_count=0
def edgeset(es):return frozenset(frozenset(e) for e in es)
for ci,aa in actions.items():
 r=comp['results'][ci];F=cover['cases'][r['F_index']];X=F['representatives'][r['X_index']];hosts=X['singleton_hosts'];symbol=[[0]*7 for _ in range(7)]
 for bit,es in [(1,F['F_edges']),(2,X['X_edges'])]:
  for a,b in es:symbol[a][b]|=bit;symbol[b][a]|=bit
 degree=[(sum(x&1>0 for x in row),sum(x&2>0 for x in row)) for row in symbol]
 expected=set()
 for ep in itertools.permutations(range(7)):
  if any(degree[a]!=degree[ep[a]] for a in range(7)):continue
  if any(symbol[a][b]!=symbol[ep[a]][ep[b]] for a in range(7) for b in range(a)):continue
  for cp in itertools.permutations(range(3)):
   if all(ep[hosts[11+k][0]]==hosts[11+cp[k]][0] for k in range(3)):expected.add((ep,cp))
 assert expected=={(tuple(a['E']),tuple(a['C'])) for a in aa} and len(aa)==len(expected)
 for ai,a in enumerate(aa):
  ep,dp,cp=a['E'],a['D'],a['C'];assert sorted(dp)==list(range(11))
  for d in range(11):assert {ep[e] for e in hosts[d]}==set(hosts[dp[d]])
  vp=list(ep)+[7+d for d in dp]+[18+c for c in cp];perms[ci,ai]=vp
  assert sorted(vp)==list(range(21))
  for j,es in enumerate(r['solutions']):
   target=edgeset((vp[a],vp[b]) for a,b in es);target_j=a['solutions'][j]
   assert target==edgeset(r['solutions'][target_j]);edge_cache[ci,ai,j]=target_j
  action_count+=1
 assert time.monotonic()-start<60
counts=collections.Counter();used_actions=collections.defaultdict(int)
for member,c in enumerate(colours):
 rep,ai=mapping[2*member:2*member+2];assert rep<=member<len(colours)
 ci,j=meta[rep];assert meta[member][0]==ci and 0<=ai<len(actions[ci])
 assert edge_cache[ci,ai,j]==meta[member][1];vp=perms[ci,ai]
 # Independently move the seven unordered high pairs, then rename their highs.
 pairs=[[18+h] if h<3 else [] for h in range(7)]
 for d,h in enumerate(colours[rep]):pairs[h].append(7+d)
 transformed=[sorted(vp[v] for v in pair) for pair in pairs];assert all(len(pair)==2 for pair in transformed)
 out=[-1]*11;double=[]
 for a,b in transformed:
  if b>=18:out[a-7]=b-18
  else:double.append((a,b))
 for h,(a,b) in enumerate(sorted(double),3):out[a-7]=out[b-7]=h
 assert out==c
 counts[rep]+=1;used_actions[rep]|=1<<ai
 if member%10000==0:assert time.monotonic()-start<60
assert set(counts)=={r['global_index'] for r in reps}
layout_by={(x['completion_index'],x['singleton_index']):x for x in layout}
for r in reps:
 rep=r['global_index'];ci,j=meta[rep]
 assert (ci,j)==(r['completion_index'],r['singleton_index'])
 loc=layout_by[ci,j]
 assert loc['global_start']+r['colouring_index']==rep
 assert counts[rep]==r['orbit_size']==len(actions[ci])
 assert used_actions[rep]==(1<<len(actions[ci]))-1
assert time.monotonic()-start<60
result=dict(status='PASS',source_assignments=len(colours),representatives=len(reps),actions=action_count,witnesses=len(colours),seconds=time.monotonic()-start)
(P/'verification.json').write_text(json.dumps(result,indent=2)+'\n');print(result)
