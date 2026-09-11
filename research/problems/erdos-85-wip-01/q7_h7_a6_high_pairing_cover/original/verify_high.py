"""Valid output sets + independent largest-vertex matching DP counts."""
import collections,functools,gzip,itertools,json,pathlib,time
P=pathlib.Path(__file__).parent
cover=json.loads((P/'source-cover-results.json').read_text());comp=json.loads((P/'source-completion-results.json').read_text());summary=json.loads((P/'high-results.json').read_text())
expected=[(i,j) for i,r in enumerate(comp['results']) for j,_ in enumerate(r['solutions'])]
start=time.monotonic();seen=[];outputs=states=unknown=negative=0;maxstates=0
with gzip.open(P/'high-colourings.jsonl.gz','rt') as stream:
 for line in stream:
  item=json.loads(line);i,j=item['completion_index'],item['singleton_index'];seen.append((i,j));r=comp['results'][i];F=cover['cases'][r['F_index']];X=F['representatives'][r['X_index']]
  assert item['F_index']==r['F_index'] and item['X_index']==r['X_index'];g=[set() for _ in range(21)]
  for a,b in F['F_edges']+r['solutions'][j]:g[a].add(b);g[b].add(a)
  for s,hs in enumerate(X['singleton_hosts'],7):
   for e in hs:g[s].add(e);g[e].add(s)
  legal=[[d for d in range(11) if 7+d not in g[18+h] and not g[18+h]&g[7+d]] for h in range(3)]
  codes=[tuple(c) for c in item['colourings']];assert len(codes)==len(set(codes));outputs+=len(codes)
  for c in codes:
   assert len(c)==11 and sorted(collections.Counter(c).items())==[(0,1),(1,1),(2,1),(3,2),(4,2),(5,2),(6,2)]
   for h in range(3):assert c.index(h) in legal[h]
   paired=[[d for d in range(11) if c[d]==h] for h in range(3,7)]
   assert [min(ds) for ds in paired]==sorted(min(ds) for ds in paired)
   for a,b in paired:assert not g[7+a]&g[7+b]
  if item['status']=='UNKNOWN':unknown+=1;continue # no completion replay of a capped domain
  assert item['status']=='COMPLETE';local=0
  @functools.lru_cache(None)
  def count(mask):
   if not mask:return 1
   a=mask.bit_length()-1;rest=mask^(1<<a)
   return sum(count(rest^(1<<b)) for b in range(a) if rest>>b&1 and not g[7+a]&g[7+b])
  n=0
  for ds in itertools.product(*legal):
   local+=1
   if len(set(ds))!=3:continue
   mask=2047
   for d in ds:mask^=1<<d
   n+=count(mask)
  local+=count.cache_info().misses;states+=local;maxstates=max(maxstates,local)
  assert local<=100000 and time.monotonic()-start<60
  assert n==len(codes),(i,j,n,len(codes));negative+=not n
assert seen==expected[:len(seen)] and len(seen)==summary['visited'] and len(expected)-len(seen)==summary['unvisited']
assert outputs==summary['colourings'] and unknown==summary['unknown'] and negative==summary['empty']
out=dict(status='PASS',visited=len(seen),unknown_preserved=unknown,unvisited_preserved=summary['unvisited'],colourings=outputs,complete_empty=negative,states=states,max_states=maxstates,seconds=time.monotonic()-start)
(P/'high-verification.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
