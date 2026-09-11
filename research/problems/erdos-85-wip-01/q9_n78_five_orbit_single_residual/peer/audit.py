from pathlib import Path
import itertools as it,json,hashlib,time
p=Path(__file__).parent;src=Path('/Users/rwalters/lean-genius-q9-known-values-20260911/n78-five-orbit-single-residual');par=Path('/tmp/erdos85-sol1-q9-n78-four-orbit-order24-parameters')
for manifest in ['pins.json','input-pins.json']:
 for n,h in json.loads((src/manifest).read_text()).items():
  f=Path(n) if Path(n).is_absolute() else src/n
  assert hashlib.sha256(f.read_bytes()).hexdigest()==h,str(f)
data=json.loads((src.parent/'n78-five-orbit-single-cross/results.json').read_text());groups=json.loads((par/'groups.json').read_text());actions=json.loads((par/'results.json').read_text())['records'];saved=json.loads((src/'results.json').read_text())
roots=[(i,j,c) for i,r in enumerate(data['records']) for j,c in enumerate(r['survivors'])];assert [(i,j) for i,j,c in roots]==[(r['root'],r['configuration']) for r in saved['records']]
cache={};start=time.monotonic();done=[];positive=total=codegrees=0
try:
 for k,(ri,ci,cfg) in enumerate(roots):
  if time.monotonic()-start>30:raise TimeoutError
  record=data['records'][ri];gi,ai=record['group'],record['action'];m=groups[gi]['multiplication'];act=actions[gi]['actions'][ai];labels=act['labels']
  if (gi,ai) not in cache:
   candidates=[]
   for l in range(1,24):
    if m[l][l]!=0:continue
    # Test every element's center label, not only representatives.
    if any(labels[m[l][x]]==labels[x] for x in range(24)):continue
    omitted={labels[0],labels[l]};fibers=[[x for x in range(24) if labels[x]==f] for f in range(6) if f not in omitted]
    for vs in it.product(*fibers):
     V=set(vs)
     if {m[l][v] for v in V}!=V:continue
     B=frozenset([0,l]+[24+v for v in V]);trans={frozenset(24*(x//24)+m[g][x%24] for x in B) for g in range(24)}
     if len(trans)!=12:continue
     if any(len(B&T)>1 for T in trans if T!=B):continue
     candidates.append((l,tuple(sorted(V)),B,trans))
   cache[gi,ai]=candidates
  adj=[set() for _ in range(54)]
  def edge(a,b):adj[a].add(b);adj[b].add(a)
  for f in range(6):edge(f,act['matching'][f])
  for a in range(24):
   edge(labels[a],6+a);edge(labels[a],30+a)
   for s in cfg['U']:edge(6+a,6+m[a][s])
   for s in cfg['V']:edge(30+a,30+m[a][s])
   for s in cfg['T']:edge(6+a,30+m[a][s])
  masks=[sum(1<<x for x in row) for row in adj];got=set()
  for l,V,B,trans in cache[gi,ai]:
   if any(masks[6+a]&masks[6+b] for a,b in it.combinations(B,2)):continue
   got.add((l,(0,l),V))
   full=[row.copy() for row in adj]+[set() for _ in range(12)]
   for z,T in enumerate(sorted(trans,key=lambda x:tuple(sorted(x))),54):
    for x in T:full[z].add(6+x);full[6+x].add(z)
   assert [len(row) for row in full]==[9]*6+[7]*24+[8]*24+[6]*12
   for a in range(66):
    for b in range(a):assert len(full[a]&full[b])<=1;codegrees+=1
  expected={(x['l'],tuple(x['U']),tuple(x['V'])) for x in saved['records'][k]['survivors']}
  assert got==expected,(ri,ci)
  done.append((ri,ci,len(got)));positive+=bool(got);total+=len(got)
 status='COMPLETE'
except TimeoutError:status='UNKNOWN'
result=dict(status=status,cap_seconds=30,seconds=time.monotonic()-start,roots=len(roots),verified=len(done),positive_roots=positive,neighborhoods=total,codegrees=codegrees,records=done)
p.joinpath('audit.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k!='records'}))
