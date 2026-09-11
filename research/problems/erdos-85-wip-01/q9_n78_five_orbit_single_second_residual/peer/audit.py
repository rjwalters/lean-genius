from pathlib import Path
import json,itertools as it,hashlib,time
p=Path(__file__).parent;src=Path('/Users/rwalters/lean-genius-q9-known-values-20260911/n78-five-orbit-single-second-residual');base=src.parent;par=Path('/tmp/erdos85-sol1-q9-n78-four-orbit-order24-parameters')
for manifest in ['pins.json','input-pins.json']:
 for n,h in json.loads((src/manifest).read_text()).items():
  f=Path(n) if Path(n).is_absolute() else src/n
  assert hashlib.sha256(f.read_bytes()).hexdigest()==h
cross=json.loads((base/'n78-five-orbit-single-cross/results.json').read_text());first=json.loads((base/'n78-five-orbit-single-residual/results.json').read_text());saved=json.loads((src/'results.json').read_text());groups=json.loads((par/'groups.json').read_text());params=json.loads((par/'results.json').read_text())['records']
roots=[(i,j,b) for i,r in enumerate(first['records']) for j,b in enumerate(r['survivors'])]
assert len(roots)==896 and [(i,j) for i,j,b in roots]==[(r['first_record'],r['first_solution']) for r in saved['records']]
start=time.monotonic();cache={};records=[];tested=0
try:
 for fi,bi,bsol in roots:
  if time.monotonic()-start>30:raise TimeoutError
  fr=first['records'][fi];r=cross['records'][fr['root']];cfg=r['survivors'][fr['configuration']];gi,ai=r['group'],r['action'];m=groups[gi]['multiplication'];act=params[gi]['actions'][ai];labels=act['labels']
  if (gi,ai) not in cache:
   candidates=[]
   for l in range(1,24):
    if m[l][l]!=0 or any(labels[m[l][x]]==labels[x] for x in range(24)):continue
    wanted=set(range(6))-{labels[0],labels[l]}
    fibers=[[a for a in range(24) if labels[a]==f] for f in sorted(wanted)]
    for us in it.product(*fibers):
     if {m[l][u] for u in us}!=set(us):continue
     candidates.append(tuple(us)+(24,24+l))
   cache[gi,ai]=candidates
  A=[set() for _ in range(66)]
  def e(a,b):A[a].add(b);A[b].add(a)
  for f in range(6):e(f,act['matching'][f])
  for a in range(24):
   e(labels[a],6+a);e(labels[a],30+a)
   for s in cfg['U']:e(6+a,6+m[a][s])
   for s in cfg['V']:e(30+a,30+m[a][s])
   for s in cfg['T']:e(6+a,30+m[a][s])
  B={tuple(sorted([m[g][u] for u in bsol['U']]+[24+m[g][v] for v in bsol['V']])) for g in range(24)};assert len(B)==12
  for i,T in enumerate(sorted(B),54):
   for v in T:e(i,6+v)
  masks=[sum(1<<a for a in row) for row in A]
  survivors=0
  for T in cache[gi,ai]:
   tested+=1
   if all(not(masks[6+a]&masks[6+b]) for a,b in it.combinations(T,2)):survivors+=1
  assert survivors==0,(fi,bi,survivors)
  records.append([fi,bi,survivors])
 status='COMPLETE'
except TimeoutError:status='UNKNOWN'
res=dict(status=status,cap_seconds=30,seconds=time.monotonic()-start,roots=len(roots),verified=len(records),invariant_candidates=tested,survivors=0,records=records)
p.joinpath('audit.json').write_text(json.dumps(res,indent=2)+'\n');print(json.dumps({k:v for k,v in res.items() if k!='records'}))
