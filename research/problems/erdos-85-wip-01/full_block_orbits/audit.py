import json,itertools,time,argparse
from pathlib import Path
start=time.monotonic()
parser=argparse.ArgumentParser();parser.add_argument('--witnesses',type=Path,required=True);args=parser.parse_args()
reps=json.loads(args.witnesses.read_text())['representatives']
edges=list(itertools.combinations(range(5),2))
def adj(t):
 a,b,p=t;A=[0]*15
 def add(x,y):A[x]|=1<<y;A[y]|=1<<x
 for k,m in enumerate([129,a,b]):
  for n,(i,j) in enumerate(edges):
   if m>>n&1:add(5*k+i,5*k+j)
 for i in range(5):add(i,5+i);add(i,10+i);add(5+i,10+p[i])
 return A
As=list(map(adj,reps));keys={tuple(A):r for r,A in enumerate(As)}
assert len(keys)==55
records=[]
for r,A in enumerate(As):
 options=[]
 for tau in itertools.permutations(range(3)):
  anchor=tau.index(0)
  for sigma in itertools.permutations(range(5)):
   f=[None]*15
   for i in range(5):f[5*anchor+i]=sigma[i]
   for b in range(3):
    if b==anchor:continue
    for i in range(5):
     ns=[j for j in range(5) if A[5*anchor+i]>>(5*b+j)&1]
     assert len(ns)==1
     f[5*b+ns[0]]=5*tau[b]+sigma[i]
   assert sorted(f)==list(range(15))
   B=[0]*15
   for i in range(15):
    for j in range(15):
     if A[i]>>j&1:B[f[i]]|=1<<f[j]
   q=keys.get(tuple(B))
   if q is not None:options.append((q,list(tau),f))
 q,tau,f=min(options)
 assert all(bool(A[i]>>j&1)==bool(As[q][f[i]]>>f[j]&1) for i in range(15) for j in range(15))
 assert all(f[i]//5==tau[i//5] for i in range(15))
 records.append(dict(source=r,target=q,blocks=tau,permutation=f))
classes=sorted(set(x['target'] for x in records))
out=dict(source_count=55,class_count=len(classes),targets=classes,records=records,elapsed_seconds=time.monotonic()-start,scope='Explicit Python block-preserving equivalences only; not Lean proof or graph rejection')
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k!='records'},indent=2))
