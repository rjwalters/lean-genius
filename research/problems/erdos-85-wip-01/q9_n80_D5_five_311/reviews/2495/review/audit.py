from pathlib import Path
import json,hashlib,itertools as it,time,functools,sqlite3
b=Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3');o=Path(__file__).parent
def read(name):return json.loads((b/name).read_text())
names=['residual-ten-D5-five-311-center-cross-domains','residual-ten-D5-five-311-center-cross-cover'];nh=0
for name in names:
 for fn in ['pins.json','input-pins.json']:
  for k,v in read(name+'/'+fn).items():
   p=Path(k);p=p if p.is_absolute() else b/name/p
   assert hashlib.sha256(p.read_bytes()).hexdigest()==v;nh+=1
c=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True)
for rid in [2478,2488,2492]:
 s,r=c.execute('select status,resolution from review_requests where id=?',(rid,)).fetchone();assert s=='resolved' and r.startswith('PASS')
def records(name):return {r['root']:r for r in read('residual-ten-D5-five-311-'+name+'/results.json')['records']}
dom=records('center-domains');prior=records('structured-center-cover');prop=records('low-propagation');edges=records('low-edge-capacity');joint=records('nonempty-joint');graphs=records('high-matchings');cross=records('center-cross-domains');covers=records('center-cross-cover');assert cross.keys()==covers.keys()==prior.keys() and len(cross)==39
start=time.monotonic();status='INCOMPLETE';tested=accepted=0
def guard():
 if time.monotonic()-start>=30:raise TimeoutError
try:
 for root,r in cross.items():
  guard();d=dom[root];src=d['source_root'];ai=d['source_assignment'];lows=next(x['lows'] for x in edges[src]['survivors'] if x['assignment']==ai);pr=next(x for x in prop[src]['survivors'] if x['assignment']==ai);j=joint[src];F=[set() for _ in range(60)]
  es=list(map(tuple,graphs[j['packing_root']]['survivors'][j['graph']]['edges']))+[(v,10+i) for i,(v,_) in enumerate(lows) if v>=0]+[(10+i,10+k) for i,k in pr['forced_edges']]
  for u,v in es:F[u].add(v);F[v].add(u)
  P=[set(x) for x in F]
  for u,v in pr['remaining_edges']:P[10+u].add(10+v);P[10+v].add(10+u)
  labels=[lows[u][0]//2 if lows[u][0]>=0 else -1 for u,v in d['low_orbits']];expected=[]
  for idx,g in enumerate(d['low_groups']):
   ls=[labels[i] for i in g];act=set(ls)-{-1};z=ls.count(-1)
   if z<=1 and len(act)==3-z:expected.append(dict(source_group=idx,orbits=g,active=sum(1<<a for a in act),inactive=z))
  assert expected==r['low_groups'] and d['high_groups']==r['high_groups']
  def vertices(g):return {10+v for i in g for v in d['low_orbits'][i]}
  LV=[vertices(x['orbits']) for x in expected];ncase=0
  for f,hs in enumerate(d['high_groups']):
   for hi,g in enumerate(hs):
    H=vertices(g)|{2*f,2*f+1};ok=[]
    for li,L in enumerate(LV):
     guard();tested+=1;ncase+=1
     if H&L:continue
     forced={(u,v) for u in H for v in F[u]&L}
     if not expected[li]['active']&(1<<f):
      if not forced:ok.append(li)
      continue
     if len({u for u,v in forced})!=len(forced) or len({v for u,v in forced})!=len(forced):continue
     left=sorted(H-{u for u,v in forced});right=L-{v for u,v in forced}
     # Hall's theorem: every subset must have at least as many possible neighbors.
     good=True
     for mask in range(1,1<<len(left)):
      neighbors=set()
      for k,u in enumerate(left):
       if mask>>k&1:neighbors|=P[u]&right
      if len(neighbors)<mask.bit_count():good=False;break
     if good:ok.append(li)
    assert ok==r['compatibility'][f][hi];accepted+=len(ok)
  assert ncase==r['tested']
 assert tested==894198 and accepted==607112;status='COMPLETE'
except TimeoutError:pass
s1=dict(status=status,original_cap_seconds=30,seconds=time.monotonic()-start,tested=tested,compatible=accepted);(o/'stage1.json').write_text(json.dumps(s1,indent=2)+'\n');print(s1,flush=True);assert status=='COMPLETE'
# Independent bitset exact-cover search. Reorder high centers once per case;
# low choices branch on the smallest uncovered orbit, not the producer's MRV.
@functools.lru_cache(None)
def center(patterns):
 C=[(x,5+j) for j,A in enumerate(patterns) for x in range(5) if not A>>x&1];degree=[sum(x in e for e in C) for x in range(5)];ys=[5+j for j,A in enumerate(patterns) if A.bit_count()==3]
 if len(ys)!=4:return False
 for xx in it.combinations(list(it.combinations(range(5),2)),2):
  if any(degree[x]+sum(x in e for e in xx)!=3 for x in range(5)):continue
  for mate in ys[1:]:
   rem=[y for y in ys[1:] if y!=mate];E=C+list(xx)+[(ys[0],mate),tuple(rem)];N=[set() for _ in range(10)]
   for u,v in E:N[u].add(v);N[v].add(u)
   if all(len(x)==3 for x in N) and all(len(a&b)<=1 for a,b in it.combinations(N,2)):return True
 return False
start=time.monotonic();status='INCOMPLETE';count=neg=pos=0;receipt=[]
try:
 for root,r in cross.items():
  guard();lo=r['low_groups'];masks=[sum(1<<v for v in x['orbits']) for x in lo];hs=[[(sum(1<<v for v in g),sum(1<<j for j in r['compatibility'][i][k])) for k,g in enumerate(gs)] for i,gs in enumerate(r['high_groups'])];order=sorted(range(5),key=lambda i:len(hs[i]));by=[tuple(i for i,m in enumerate(masks) if m>>v&1) for v in range(25)]
  @functools.lru_cache(None)
  def low(rem,allowed,pats,z):
   guard()
   if not rem:return z==1 and center(pats)
   v=(rem&-rem).bit_length()-1
   for i in by[v]:
    m=masks[i];x=lo[i];A=x['active'];nz=z+x['inactive']
    if not allowed>>i&1 or m&rem!=m or nz>1:continue
    if any(((31^A)&(31^B)).bit_count()>1 for B in pats):continue
    np=tuple(sorted(pats+(A,)))
    if any(sum(not B>>j&1 for B in np)>3 for j in range(5)):continue
    if low(rem^m,allowed,np,nz):return True
   return False
  @functools.lru_cache(None)
  def high(k,used,allowed):
   guard()
   if allowed.bit_count()<5:return False
   if k==5:return low(((1<<25)-1)^used,allowed,(),0)
   for m,a in hs[order[k]]:
    if not m&used and high(k+1,used|m,allowed&a):return True
   return False
  actual=high(0,0,(1<<len(lo))-1);saved=covers[root];assert saved['status']=='COMPLETE' and actual==(saved['witness'] is not None)
  # Validate producer's positive witness separately, including exact center graph.
  if actual:
   HH,(LL,E)=saved['witness'];assert len(HH)==5 and {i for i,j in HH}==set(range(5)) and len(LL)==5;used=set()
   for i,j in HH:
    g=set(r['high_groups'][i][j]);assert not used&g;used|=g
    assert all(li in r['compatibility'][i][j] for li in LL)
   for li in LL:
    g=set(lo[li]['orbits']);assert not used&g;used|=g
   assert used==set(range(25)) and sum(lo[li]['inactive'] for li in LL)==1
   N=[set() for _ in range(10)];assert len({tuple(sorted(e)) for e in E})==len(E)==15
   for u,v in E:assert u!=v;N[u].add(v);N[v].add(u)
   assert all(len(x)==3 for x in N) and all(len(a&b)<=1 for a,b in it.combinations(N,2))
   for j,li in enumerate(LL):assert N[5+j]&set(range(5))=={x for x in range(5) if not lo[li]['active']>>x&1}
  count+=1;pos+=actual;neg+=not actual;receipt.append(dict(root=root,positive=actual))
 assert (count,neg,pos)==(39,10,29);status='COMPLETE'
except TimeoutError:pass
s2=dict(status=status,original_cap_seconds=30,seconds=time.monotonic()-start,cases=count,negative=neg,positive=pos,records=receipt);(o/'stage2.json').write_text(json.dumps(s2,indent=2)+'\n');(o/'audit.json').write_text(json.dumps(dict(hashes=nh,stages=[s1,s2]),indent=2)+'\n');print(s2,flush=True);assert status=='COMPLETE'
