from pathlib import Path
import json,hashlib,itertools as it,time,functools,sqlite3
b=Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3');o=Path(__file__).parent
def read(name):return json.loads((b/name).read_text())
names=['low-center-cross-cover','high-center-defect-degree','center-defect-cover'];nh=0
for name in names:
 base=b/('residual-ten-D5-five-311-'+name)
 for fn in ['pins.json','input-pins.json']:
  for k,v in json.loads((base/fn).read_text()).items():
   p=Path(k);p=p if p.is_absolute() else base/p
   assert hashlib.sha256(p.read_bytes()).hexdigest()==v;nh+=1
c=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True)
for rid in [2488,2492,2495]:
 s,r=c.execute('select status,resolution from review_requests where id=?',(rid,)).fetchone();assert s=='resolved' and r.startswith('PASS')
def data(name):return read('residual-ten-D5-five-311-'+name+'/results.json')
def records(name):return {r['root']:r for r in data(name)['records']}
dom=records('center-domains');prop=records('low-propagation');edgecases=records('low-edge-capacity');joint=records('nonempty-joint');graphs=records('high-matchings');cross=records('center-cross-domains');prior=records('center-cross-cover');first=records('low-center-cross-cover');partial=records('center-defect-cover');required={k for k,v in prior.items() if v['witness'] is not None};assert first.keys()==partial.keys()==required and len(required)==29
assert data('low-center-cross-cover')['status']=='COMPLETE' and data('center-defect-cover')['status']=='INCOMPLETE'
assert {k for k,v in partial.items() if v['status']=='UNKNOWN'}=={27}
assert sum(v['status']=='UNVISITED' for v in partial.values())==13
assert {k for k,v in partial.items() if v['status']=='COMPLETE' and v['witness'] is None}=={8}
assert sum(v['status']=='COMPLETE' and v['witness'] is not None for v in partial.values())==14
start=time.monotonic();status='INCOMPLETE';verified=0
def guard():
 if time.monotonic()-start>=30:raise TimeoutError

def setup(root):
 d=dom[root];r=cross[root];src=d['source_root'];ai=d['source_assignment'];lows=next(x['lows'] for x in edgecases[src]['survivors'] if x['assignment']==ai);pr=next(x for x in prop[src]['survivors'] if x['assignment']==ai);j=joint[src];hg=graphs[j['packing_root']]['survivors'][j['graph']]['edges'];matched={v//2 for e in hg for v in e};F=[set() for _ in range(50)]
 for u,v in pr['forced_edges']:F[u].add(v);F[v].add(u)
 P=[set(x) for x in F]
 for u,v in pr['remaining_edges']:P[u].add(v);P[v].add(u)
 V=[{v for i in x['orbits'] for v in d['low_orbits'][i]} for x in r['low_groups']]
 @functools.lru_cache(None)
 def pair(i,j,adjacent):
  A=V[i];B=V[j]
  if A&B:return False
  edges={(u,v) for u in A for v in F[u]&B}
  if adjacent:return not edges
  if len({u for u,v in edges})!=len(edges) or len({v for u,v in edges})!=len(edges):return False
  L=sorted(A-{u for u,v in edges});R=B-{v for u,v in edges}
  for mask in range(1,1<<len(L)):
   ns=set()
   for k,u in enumerate(L):
    if mask>>k&1:ns|=P[u]&R
   if len(ns)<mask.bit_count():return False
  return True
 goals=[[2-sum(lows[d['low_orbits'][i][0]][0]<0 for i in g)+int(f in matched) for g in gs] for f,gs in enumerate(r['high_groups'])]
 return r,pair,goals
try:
 for root in sorted(required):
  guard();r,pair,goals=setup(root)
  for rec,degree in [(first[root],False)]+([(partial[root],True)] if partial[root]['status']=='COMPLETE' and partial[root]['witness'] is not None else []):
   assert rec['status']=='COMPLETE' and rec['witness'] is not None
   HH,(LL,E)=rec['witness'];assert len(HH)==len(LL)==5 and {i for i,j in HH}==set(range(5));used=set();lo=r['low_groups']
   for i,j in HH:
    g=set(r['high_groups'][i][j]);assert not used&g;used|=g;assert all(k in r['compatibility'][i][j] for k in LL)
   for k in LL:
    g=set(lo[k]['orbits']);assert not used&g;used|=g
   assert used==set(range(25)) and sum(lo[k]['inactive'] for k in LL)==1
   N=[set() for _ in range(10)];assert len(E)==len({tuple(sorted(e)) for e in E})==15
   for u,v in E:assert u!=v;N[u].add(v);N[v].add(u)
   assert all(len(x)==3 for x in N) and all(len(a&b)<=1 for a,b in it.combinations(N,2))
   for k,li in enumerate(LL):assert N[5+k]&set(range(5))=={v for v in range(5) if not lo[li]['active']>>v&1}
   for i,j in it.combinations(range(5),2):assert pair(*sorted((LL[i],LL[j])),5+j in N[5+i])
   if degree:
    for i,j in HH:assert len(N[i]&set(range(5,10)))==goals[i][j]
   verified+=1
 assert verified==43;status='COMPLETE'
except TimeoutError:pass
s1=dict(status=status,seconds=time.monotonic()-start,original_cap_seconds=30,witnesses=verified);(o/'stage1.json').write_text(json.dumps(s1,indent=2)+'\n');print(s1,flush=True);assert status=='COMPLETE'
# Independent verification ONLY of completed negative root8. Never visit capped27 or13 unvisited roots.
start=time.monotonic();status='INCOMPLETE';r,pair,goals=setup(8);lo=r['low_groups'];masks=[sum(1<<v for v in x['orbits']) for x in lo];hs=[[(sum(1<<v for v in g),sum(1<<k for k in r['compatibility'][i][j])) for j,g in enumerate(gs)] for i,gs in enumerate(r['high_groups'])];by=[tuple(i for i,m in enumerate(masks) if m>>v&1) for v in range(25)]
@functools.lru_cache(None)
def finish(selected,required_degrees):
 pats=[lo[i]['active'] for i in selected];E=[(v,5+j) for j,A in enumerate(pats) for v in range(5) if not A>>v&1];ds=tuple(sum(v in e for e in E) for v in range(5))
 if ds!=required_degrees:return False
 ys=[j for j,A in enumerate(pats) if A.bit_count()==3]
 if len(ys)!=4:return False
 for mate in ys[1:]:
  rem=[y for y in ys[1:] if y!=mate];YY={(min(ys[0],mate),max(ys[0],mate)),tuple(rem)}
  if not all(pair(*sorted((selected[i],selected[j])),(i,j) in YY) for i,j in it.combinations(range(5),2)):continue
  for XX in it.combinations(list(it.combinations(range(5),2)),2):
   if any(ds[v]+sum(v in e for e in XX)!=3 for v in range(5)):continue
   N=[set() for _ in range(10)]
   for u,v in E+list(XX)+[(5+i,5+j) for i,j in YY]:N[u].add(v);N[v].add(u)
   if all(len(a&b)<=1 for a,b in it.combinations(N,2)):return True
 return False
@functools.lru_cache(None)
def low(rem,allowed,selected,z,ds):
 guard()
 if not rem:return z==1 and finish(selected,ds)
 v=(rem&-rem).bit_length()-1
 for i in by[v]:
  x=lo[i];m=masks[i]
  if not allowed>>i&1 or m&rem!=m or z+x['inactive']>1:continue
  if any(((31^x['active'])&(31^lo[j]['active'])).bit_count()>1 for j in selected):continue
  seq=tuple(sorted(selected+(i,)))
  if any(sum(not lo[k]['active']>>v&1 for k in seq)>ds[v] for v in range(5)):continue
  if any(not pair(*sorted((i,j)),False) and not pair(*sorted((i,j)),True) for j in selected):continue
  if low(rem^m,allowed,seq,z+x['inactive'],ds):return True
 return False
@functools.lru_cache(None)
def high(k,used,allowed,ds):
 guard()
 if allowed.bit_count()<5:return False
 if k==5:return low(((1<<25)-1)^used,allowed,(),0,ds)
 for j,(m,ok) in enumerate(hs[k]):
  if m&used or not 1<=goals[k][j]<=3:continue
  if high(k+1,used|m,allowed&ok,ds+(goals[k][j],)):return True
 return False
try:
 assert not high(0,0,(1<<len(lo))-1,());status='COMPLETE'
except TimeoutError:pass
s2=dict(status=status,seconds=time.monotonic()-start,original_cap_seconds=30,root=8,negative=status=='COMPLETE');(o/'stage2.json').write_text(json.dumps(s2,indent=2)+'\n');(o/'audit.json').write_text(json.dumps(dict(hashes=nh,stages=[s1,s2],original_partial_status='INCOMPLETE',unknown=[27],unvisited=13),indent=2)+'\n');print(s2,flush=True);assert status=='COMPLETE'
