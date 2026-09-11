import pathlib,json,itertools,collections,hashlib,time
P=pathlib.Path(__file__).parent;S=pathlib.Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3/h7-a7-singleton-core');load=lambda f:json.loads((S/f).read_text())
for f,h in load('pins.json').items():assert hashlib.sha256((S/f).read_bytes()).hexdigest()==h
src=load('results.json');colour=load('colour-results.json');es=list(itertools.combinations(range(7),2));index={e:i for i,e in enumerate(es)};valid=set();nodes=0;start=time.monotonic();g=[set() for _ in range(7)]
# Independent vertex-neighbour recursion: finalize one vertex at each level,
# rather than iterating all fixed-edge subsets.
def visit(v,m,mask):
 global nodes
 nodes+=1
 if nodes>966416 or time.monotonic()-start>60:raise TimeoutError
 if v==7:
  if 7<=m<=10:valid.add(mask)
  return
 options=[w for w in range(v+1,7) if len(g[w])<3]
 for n in range(min(3-len(g[v]),len(options),10-m)+1):
  for choice in itertools.combinations(options,n):
   for w in choice:g[v].add(w);g[w].add(v)
   if all(len(g[a]&g[b])<=1 for a in range(7) for b in range(a)):
    visit(v+1,m+n,mask|sum(1<<index[(v,w)] for w in choice))
   for w in choice:g[v].remove(w);g[w].remove(v)
visit(0,0,0)
seen=set();hist=collections.Counter()
for r in src['classes']:
 orbit={sum(1<<index[tuple(sorted((p[a],p[b])))] for a,b in r['edges']) for p in itertools.permutations(range(7))}
 assert not seen&orbit and len(orbit)==r['orbit_size'];seen|=orbit;hist[r['edge_count']]+=1
assert seen==valid and len(valid)==53280 and dict(hist)=={7:15,8:7,9:2}
assert collections.Counter(m.bit_count() for m in valid)=={7:32910,8:17010,9:3360}
counts=[]
for i,(core,row) in enumerate(zip(src['classes'],colour['rows'])):
 assert row['core_index']==i
 s=[set() for _ in range(14)]
 def edge(u,v):s[u].add(v);s[v].add(u)
 for u,v in core['edges']:edge(u,v)
 leaf=7
 for u in range(7):
  for _ in range(3-len(s[u])):edge(u,leaf);leaf+=1
 for u in range(leaf,14,2):edge(u,u+1)
 assert sorted([list(e) for e in itertools.combinations(range(14),2) if e[1] in s[e[0]]])==row['singleton_edges']
 assert list(map(len,s))==[3]*7+[1]*7
 # Permanent of the allowed colour-pair matrix, independent of 7! scan.
 allowed=[[not s[u]&s[v] for v in range(7,14)] for u in range(7)];coeff={0:1}
 for u in range(7):
  nxt=collections.defaultdict(int)
  for used,count in coeff.items():
   for j in range(7):
    if not used>>j&1 and allowed[u][j]:nxt[used|(1<<j)]+=count
  coeff=nxt
 assert coeff[127]==row['colour_pairings']>0;counts.append(coeff[127])
 full=[ns.copy() for ns in s]+[set() for _ in range(7)]
 for h,v in enumerate(row['witness_leaf_assignment']):
  for u in [h,v]:full[14+h].add(u);full[u].add(14+h)
 assert all(len(full[u]&full[v])<=1 for u in range(21) for v in range(u))
out=dict(status='PASS',vertex_recursion_nodes=nodes,labelled_cores=len(valid),classes=dict(hist),colour_pairing_counts=counts,witnesses=24,seconds=time.monotonic()-start,scope='Conditional necessary a7singleton-core cover only; s_i>=3 premise still pending. No shape or fullgraph exclusion.')
(P/'results.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
