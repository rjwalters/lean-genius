from pathlib import Path
import itertools,json,math,time,collections,functools
B=Path('/Users/rwalters/lean-genius-q9-known-values-20260911');P=Path(__file__).parent
start=time.monotonic()
# Independent eight-position cyclic convolution followed by antipodal subtraction.
def reduce(v):return tuple(v[j]-v[j+4] for j in range(4))
def expand(v):return tuple(v)+(0,0,0,0)
def conjugate(v):
 x=expand(v);return reduce(tuple(x[(-j)%8] for j in range(8)))
@functools.lru_cache(None)
def multiply(v,w):
 x=expand(v);y=expand(w);out=[0]*8
 for i in range(8):
  for j in range(8):out[(i+j)%8]+=x[i]*y[j]
 return reduce(out)
def dot(r,s):
 out=[0]*4
 for a,b in zip(r,s):
  t=multiply(a,conjugate(b))
  for j in range(4):out[j]+=t[j]
 return tuple(out)
def moments(v):
 h=sum((-1)**j*x for j,x in enumerate(v));g=(sum(x for j,x in enumerate(v) if j%4==0)-sum(x for j,x in enumerate(v) if j%4==2),sum(x for j,x in enumerate(v) if j%4==1)-sum(x for j,x in enumerate(v) if j%4==3))
 return (sum(v),h,g),reduce(v)
cross=collections.defaultdict(set)
# Every count0..2 is realized by a subset of {r,r+8}; no mask enumeration/import.
for v in itertools.product(range(3),repeat=8):
 k,z=moments(v);cross[k].add(z)
selfdom=collections.defaultdict(set)
for bits in itertools.product(range(2),repeat=7):
 v=[0]*8;v[0]=9
 for s,b in enumerate(bits,1):
  if b:v[s%8]+=1;v[-s%8]+=1
 k,z=moments(v);selfdom[k].add(z)
q=json.loads((B/'n80-m16-quotient/verification.json').read_text())['representatives'][1]['matrix'];q2=[[sum(q[i][k]*q[j][k] for k in range(5)) for j in range(5)] for i in range(5)]
cases=json.loads((B/'n80-m16-character-gauge/orbits.json').read_text());results=[]
for case in cases:
 h=[case['H'][i*5:i*5+5] for i in range(5)];c=[case['C'][i*5:i*5+5] for i in range(5)]
 h2=[[sum(h[i][k]*h[j][k] for k in range(5)) for j in range(5)] for i in range(5)]
 c2=[[(sum(c[i][k][0]*c[j][k][0]+c[i][k][1]*c[j][k][1] for k in range(5)),sum(c[i][k][1]*c[j][k][0]-c[i][k][0]*c[j][k][1] for k in range(5))) for j in range(5)] for i in range(5)]
 operations=[0]
 def tick():
  operations[0]+=1;assert operations[0]<=100000 and time.monotonic()-start<60,'audit cap; no retry'
 domains=[]
 for i in range(5):
  cells=[]
  for j in range(5):
   if i!=j:cells.append(cross[(q[i][j],h[i][j],tuple(c[i][j]))]);continue
   allowed=set()
   candidates=[()] if q[i][i]==0 else [(8,)] if q[i][i]==1 else [(s,16-s) for s in range(1,8) if 16//math.gcd(16,s)>=5]
   for offsets in candidates:
    v=[0]*8
    for s in offsets:v[s%8]+=1
    key,z=moments(v)
    if key==(q[i][i],h[i][i],tuple(c[i][i])):allowed.add(z)
   cells.append(allowed)
  rows=[]
  for row in itertools.product(*cells):
   tick()
   if dot(row,row) in selfdom[(q2[i][i],h2[i][i],c2[i][i])]:rows.append(row)
  domains.append(rows)
 kept=[0]
 def visit(left):
  tick()
  if not left:kept[0]+=1;return
  i=min(left,key=lambda j:len(left[j]))
  for row in left[i]:
   nxt={};ok=True
   for j,rows in left.items():
    if j==i:continue
    candidates=[r for r in rows if row[j]==conjugate(r[i]) and dot(row,r) in cross[(q2[i][j],h2[i][j],c2[i][j])]]
    if not candidates:ok=False;break
    nxt[j]=candidates
   if ok:visit(nxt)
 visit(dict(enumerate(domains)))
 assert kept[0]==0
 results.append(dict(case=case['id'],retained=kept[0],row_sizes=list(map(len,domains)),operations=operations[0]))
assert len(results)==4
out=dict(status='PASS_FOUR_CASES_EMPTY',cases=results,seconds=time.monotonic()-start,method='residue counts0..2; eight-position convolution; dynamic row constraint join; no producer imports')
(P/'results.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
