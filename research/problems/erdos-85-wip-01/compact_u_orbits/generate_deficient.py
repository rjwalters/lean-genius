from itertools import combinations,permutations,product
from pathlib import Path
import json,time,hashlib
start=time.monotonic()
masks=(129,257,513,34,66,514,20,68,260,24,40,136,528,288,192)
edges=list(combinations(range(5),2));index={e:i for i,e in enumerate(edges)}
perms=list(permutations(range(5)))
def mask_edges(m):return [e for i,e in enumerate(edges) if m>>i&1]
def relabel(m,p):return sum(1<<index[tuple(sorted((p[i],p[j])))] for i,j in mask_edges(m))
stab=[p for p in perms if relabel(129,p)==129];assert len(stab)==8

def adjacency(t):
 a,b,p,d=t;row=[0]*15
 def add(i,j):row[i]|=1<<j;row[j]|=1<<i
 for k,m in enumerate((129,a,b)):
  for i,j in mask_edges(m):add(5*k+i,5*k+j)
 for i in range(5):
  add(i,5+i);add(i,10+i)
  if i!=d:add(5+i,10+p[i])
 return row

def c4free(row):return all((row[i]&row[j]).bit_count()<=1 for i in range(15) for j in range(i+1,15))
def inverse(p):return tuple(p.index(i) for i in range(5))
def transform(t,p,swap):
 a,b,pi,d=t;inv=inverse(p)
 if swap:a,b,pi,d=b,a,inverse(pi),pi[d]
 return relabel(a,p),relabel(b,p),tuple(p[pi[inv[i]]] for i in range(5)),p[d]
valid={t:adjacency(t) for t in product(masks,masks,perms,range(5)) if c4free(adjacency(t))}
records=[];representatives=set()
for t,row in valid.items():
 options=[]
 for p,swap in product(stab,(False,True)):
  q=transform(t,p,swap);assert q in valid
  f=[5*((3-k) if swap and k else k)+p[i] for k in range(3) for i in range(5)]
  assert sorted(f)==list(range(15))
  assert all(bool(row[i]>>j&1)==bool(valid[q][f[i]]>>f[j]&1) for i in range(15) for j in range(15))
  options.append((q,p,swap))
 q,p,swap=min(options);representatives.add(q)
 records.append(dict(source=t,representative=q,diagonal_permutation=p,swap_rows_1_2=swap))
for q in representatives:assert min(transform(q,p,swap) for p,swap in product(stab,(False,True)))==q
result=dict(raw_count=135000,admissible_count=len(valid),stabilizer_size=8,action_size=16,representative_count=len(representatives),representatives=sorted(representatives),witnesses=records,elapsed_seconds=time.monotonic()-start,scope='Python deficient U-parameter orbit coverage; not Lean proof or graph rejection')
r=Path(__file__).parent;(r/'deficient_witnesses.json').write_text(json.dumps(result,indent=2)+'\n')
summary={k:v for k,v in result.items() if k not in ('witnesses','representatives')};summary['generator_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest();(r/'DEFICIENT_RECEIPT.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary))
