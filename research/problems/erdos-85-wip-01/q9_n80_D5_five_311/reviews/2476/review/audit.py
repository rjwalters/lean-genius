from pathlib import Path
import json,itertools as it,hashlib,sqlite3,time,functools
b=Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3');p=b/'residual-ten-D5-five-311-low-edge-capacity';o=Path(__file__).parent
def read(f):return json.loads(f.read_text())
nh=0
for name in ['pins.json','input-pins.json']:
 if not (p/name).exists():continue
 for k,v in read(p/name).items():
  q=Path(k);q=q if q.is_absolute() else p/q
  assert hashlib.sha256(q.read_bytes()).hexdigest()==v;nh+=1
data=read(p/'results.json');assert data['status']=='COMPLETE'
joint={r['root']:r for r in read(b/'residual-ten-D5-five-311-nonempty-joint/results.json')['records']};flow=read(b/'residual-ten-D5-five-311-nonempty-low-integer/results.json')['records'];graphs={r['root']:r for r in read(b/'residual-ten-D5-five-311-high-matchings/results.json')['records']};pack=read(b/'residual-ten-D5-five-311-packing/results.json')['records'];dom=read(b/'residual-ten-D5-supports/results.json')['records'];actual={r['root']:r for r in data['records']};assert len(actual)==len(data['records'])==len(flow) and actual.keys()=={r['root'] for r in flow}
start=time.monotonic();status='INCOMPLETE';counts={'vertex_support_capacity':0,'support_block_matching':0,'survivor':0}
def guard():
 if time.monotonic()-start>30:raise TimeoutError
def flip(m):return sum(1<<(v^1) for v in range(10) if m&(1<<v))
try:
 for f in flow:
  src=joint[f['root']];ci=src['class'];root=pack[ci]['survivors'][src['source_root']];d=dom[ci];rho={v:w for a,z in d['edges'] for v,w in [(a,z),(z,a)]};S=[]
  for j in root['high3']:
   s=set(d['high3'][j]);S.extend([s,{v^1 for v in s}])
  Hg=graphs[src['packing_root']]['survivors'][src['graph']]['edges'];H=[set() for _ in range(10)]
  for v,w in Hg:H[v].add(w);H[w].add(v)
  ar=actual[f['root']];outs={r['assignment']:r for r in ar['certificates']+ar['survivors']};assert len(outs)==len(ar['certificates'])+len(ar['survivors'])==len(f['survivors']) and outs.keys()=={r['assignment'] for r in f['survivors']}
  for kept in f['survivors']:
   guard();ai=kept['assignment'];a=src['survivors'][ai];Q=[{e for e in range(10) if mask&(1<<e)} for m in a['rows'] for mask in [m,flip(m)]];lows=[]
   for v in range(10):
    covered={rho[e] for e in S[v]}|set().union(*(S[w] for w in H[v]))|Q[v]
    lows.extend((v,r) for r in range(10) if r not in covered)
   lows.extend((-1,r) for r in range(10) for _ in range(a['inactive'][r]));assert len(lows)==50
   N=[set() for _ in range(70)]
   def edge(v,w):N[v].add(w);N[w].add(v)
   for v,w in d['edges']:edge(v,w)
   for v,s in enumerate(S):
    for r in s:edge(10+v,r)
   for v,w in Hg:edge(10+v,10+w)
   for i,(v,r) in enumerate(lows):
    edge(20+i,r)
    if v>=0:edge(20+i,10+v)
   masks=[sum(1<<v for v in ns) for ns in N];assert all((x&y).bit_count()<=1 for x,y in it.combinations(masks,2))
   targets=[set(range(10))-({rho[r]}|(S[v] if v>=0 else set())) for v,r in lows];A=[set() for _ in lows]
   for i,j in it.combinations(range(50),2):
    if lows[j][1] not in targets[i] or lows[i][1] not in targets[j]:continue
    # A newly added edge makes C4 iff an existing length-three path joins its endpoints.
    if any(bb in N[aa] for aa in N[20+i] for bb in N[20+j]):continue
    A[i].add(j);A[j].add(i)
   capacity=[]
   for i,(v,r) in enumerate(lows):
    available={lows[j][1] for j in A[i]}
    if (v>=0 and not targets[i]<=available) or (v<0 and len(available)<7):capacity.append(i)
   rec=outs[ai]
   if capacity:
    assert rec['kind']=='vertex_support_capacity' and rec['low'] in capacity;counts[rec['kind']]+=1;continue
   infeasible=[]
   for r in range(10):
    for e in range(r,10):
     nodes={i for i,(_,s) in enumerate(lows) if (s==r and e in targets[i]) or (s==e and r in targets[i])}
     required=frozenset(i for i in nodes if lows[i][0]>=0)
     BA={i:frozenset(j for j in A[i]&nodes if (lows[i][1]==r and lows[j][1]==e) or (lows[i][1]==e and lows[j][1]==r)) for i in nodes}
     @functools.lru_cache(None)
     def feasible(rem,req):
      guard()
      if not req:return True
      v=min(req,key=lambda i:len(BA[i]&rem))
      return any(feasible(rem-{v,w},req-{v,w}) for w in BA[v]&rem)
     if not feasible(frozenset(nodes),required):infeasible.append((r,e))
   if infeasible:
    assert rec['kind']=='support_block_matching' and tuple(rec['pair']) in infeasible;counts[rec['kind']]+=1
   else:
    assert rec['lows']==[list(x) for x in lows]
    edges={(i,j) for i in range(50) for j in A[i] if i<j};assert edges==set(map(tuple,rec['allowed_edges'])) and len(edges)==len(rec['allowed_edges']);counts['survivor']+=1
 assert counts=={'vertex_support_capacity':6,'support_block_matching':11,'survivor':142};status='COMPLETE'
except TimeoutError:pass
result={'status':status,'original_cap_seconds':30,'seconds':time.monotonic()-start,'hashes':nh,'counts':counts};(o/'audit.json').write_text(json.dumps(result,indent=2)+'\n');print(result)
