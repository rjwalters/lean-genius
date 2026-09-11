from pathlib import Path
import json,hashlib,sqlite3,time
out=Path(__file__).parent
src=Path('/Users/rwalters/lean-genius-q9-known-values-20260911/n78-five-orbit-split-residual')
hashes=[]
def verify(p):
 for n,h in json.loads(p.read_text()).items():
  f=Path(n) if Path(n).is_absolute() else p.parent/n
  assert hashlib.sha256(f.read_bytes()).hexdigest()==h,str(f)
  hashes.append(str(f))
verify(src/'pins.json');verify(src/'input-pins.json')
for n in json.loads((src/'input-pins.json').read_text()):
 if Path(n).name=='pins.json':verify(Path(n))
data=json.loads((src.parent/'n78-five-orbit-split-cross/results.json').read_text())
groups=json.loads(Path('/tmp/erdos85-sol1-q9-n78-four-orbit-order24-parameters/groups.json').read_text())
original=json.loads((src/'results.json').read_text())
roots=[(r['context'],i,cfg) for r in data['records'] for i,cfg in enumerate(r['survivors'])]
assert len(roots)==22848 and [(c,i) for c,i,_ in roots]==[(r['context'],r['configuration']) for r in original['records']]
assert all(r['status']=='COMPLETE' and r['survivors']==[] for r in original['records'])
# Independent action-permutation construction of ordered-pair translation masks.
translations={}
for k in {c['group'] for c in data['contexts']}:
 m=groups[k]['multiplication'];who=[[0]*24 for _ in range(24)]
 for g in range(1,24):
  for a in range(24):
   b=m[g][a];assert a!=b and who[a][b]==0;who[a][b]=1<<g
 translations[k]=who
start=time.monotonic();records=[];total=0
try:
 for ci,idx,cfg in roots:
  if time.monotonic()-start>=30:raise TimeoutError
  ctx=data['contexts'][ci];m=groups[ctx['group']]['multiplication'];labels=ctx['labels'];who=translations[ctx['group']]
  A=[set() for _ in range(54)]
  def e(a,b):A[a].add(b);A[b].add(a)
  for j in range(3):e(j,j+3)
  for a in range(24):
   e(labels[a],6+a);e(3+labels[a],30+a)
   for s in cfg['U']:e(a+6,m[a][s]+6)
   for s in cfg['V']:e(a+30,m[a][s]+30)
   for s in cfg['T']:e(a+6,m[a][s]+30)
  masks=[sum(1<<b for b in a) for a in A]
  assert all(len(A[f])==9 for f in range(6)) and all(len(A[f])==6 for f in range(6,54))
  domains=[[a for a in range(48) if labels[a%24]+3*(a//24)==f] for f in range(6)]
  assert 0 in domains[0] and all(len(d)==8 for d in domains)
  nodes=[0];survivors=[]
  def dfs(f,chosen,used):
   nodes[0]+=1
   if f==6:survivors.append(chosen);return
   for b in domains[f]:
    add=0;ok=True
    for a in chosen:
     if masks[a+6]&masks[b+6]:ok=False;break
     if a//24==b//24:
      x,y=who[a%24][b%24],who[b%24][a%24]
      if x==y or (x|y)&(used|add):ok=False;break
      add|=x|y
    if ok:dfs(f+1,chosen+[b],used|add)
  dfs(1,[0],0);assert not survivors,(ci,idx,survivors)
  total+=nodes[0];records.append(dict(context=ci,configuration=idx,nodes=nodes[0],status='COMPLETE',survivors=0))
 status='COMPLETE'
except TimeoutError:status='UNKNOWN'
result=dict(status=status,cap_seconds=30,seconds=time.monotonic()-start,roots=len(roots),verified=len(records),nodes=total,records=records,hashes=hashes)
out.joinpath('audit.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ['records','hashes']}))
