from pathlib import Path
import itertools as it,json,hashlib,time,sqlite3
out=Path(__file__).parent;src=Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3/residual-ten-11123-endpoint-packing')
for n,h in json.loads((src/'pins.json').read_text()).items():assert hashlib.sha256((src/n).read_bytes()).hexdigest()==h
if (src/'input-pins.json').exists():
 for n,h in json.loads((src/'input-pins.json').read_text()).items():assert hashlib.sha256(Path(n).read_bytes()).hexdigest()==h
classes=json.loads((src.parent/'residual-ten-11123-supports/classes.json').read_text())['classes'];expected=json.loads((src/'results.json').read_text())['records'];start=time.monotonic();records=[]
for ci,C in enumerate(classes):
 R=[0]*10
 for a,b in C['representative_edges']:R[a]|=1<<b;R[b]|=1<<a
 degree=[x.bit_count() for x in R]
 def verts(mask):return [v for v in range(10) if mask>>v&1]
 def tau(mask):return sum(1<<(v^1) for v in verts(mask))
 def valid(s,t):
  A=R[:]+[s,t]
  for v in verts(s):A[v]|=1<<10
  for v in verts(t):A[v]|=1<<11
  return all((A[i]&A[j]).bit_count()<=1 for i in range(12) for j in range(i))
 domains={2:[],3:[]}
 for k in [2,3]:
  for axes in it.combinations(range(5),k):
   for bits in it.product(range(2),repeat=k):
    vs=tuple(2*i+b for i,b in zip(axes,bits));partner=tuple(v^1 for v in vs)
    if vs>partner or sum(degree[v] for v in vs)>k+2:continue
    s=sum(1<<v for v in vs);t=tau(s)
    if not valid(s,t):continue
    if k==3:
     ends=0
     for v in vs:ends|=R[v]
     if (ends&63).bit_count()>1:continue
    domains[k].append((s,t))
 assert set(domains[3])=={(sum(1<<v for v in s),sum(1<<(v^1) for v in s)) for s in C['support_orbits']}
 def compatible(a,b):return all((x&y).bit_count()<=1 for x in a for y in b)
 for n3 in [1,2,3]:
  wanted=[3]*n3+[2]*(7-2*n3);rec=dict(class_id=ci,n311=n3,packings=0,survivors=0)
  def dfs(pos,chosen,indices):
   if time.monotonic()-start>30:raise TimeoutError('UNKNOWN original30s')
   if pos<len(wanted):
    k=wanted[pos];begin=indices[-1]+1 if pos and wanted[pos-1]==k else 0
    for i in range(begin,len(domains[k])):
     v=domains[k][i]
     if all(compatible(v,w) for w in chosen):dfs(pos+1,chosen+[v],indices+[i])
    return
   rec['packings']+=1;H=[s for pair in chosen for s in pair];K=[s.bit_count() for s in H]
   load=[sum(bool(s>>r&1) for s in H) for r in range(10)];low=[9-degree[r]-load[r] for r in range(10)]
   if min(low)<0:return
   bound=0
   for r in range(10):
    unit=3-degree[r]
    capacity=sum(k-1 for s,k in zip(H,K) if not(s&R[r]) and k-1<=unit)
    bound+=max(0,unit*low[r]-capacity)
   bases=[k+2-sum(degree[r] for r in verts(s)) for s,k in zip(H,K)]
   for i,(sv,k) in enumerate(zip(H,K)):
    nr=0
    for r in verts(sv):nr|=R[r]
    choices=[j for j,(sw,l) in enumerate(zip(H,K)) if j!=i and not(k==l==3) and not(nr&sw) and l-1<=bases[i] and k-1<=bases[j]]
    pool=sum(1<<r for r in range(10) if low[r]>0 and degree[r]<=4-k and not(R[r]&sv))
    best=[-1]
    def subsets(pos,used,number,weight):
     if weight>bases[i] or number>8-k or (k==3 and number>1):return
     if (pool&~used).bit_count()>=8-k-number:best[0]=max(best[0],weight)
     for q in range(pos,len(choices)):
      j=choices[q]
      if not used&H[j]:subsets(q+1,used|H[j],number+1,weight+K[j]-1)
    subsets(0,0,0,0)
    if best[0]<0:return
    bound+=bases[i]-best[0]
   if bound<=4*n3-2:rec['survivors']+=1
  dfs(0,[],[])
  e=next(r for r in expected if r['class']==ci and r['n311']==n3)
  assert rec['packings']==e['packings'] and rec['survivors']==e['survivors'],(rec,e)
  records.append(rec)
res=dict(status='COMPLETE',cap_seconds=30,seconds=time.monotonic()-start,records=records)
out.joinpath('audit.json').write_text(json.dumps(res,indent=2)+'\n');print(json.dumps(res))
