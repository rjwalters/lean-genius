from pathlib import Path
import itertools,json,hashlib
p=Path(__file__).resolve().parent
s=Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3/q9-order3-permutation-symmetry')
ip=json.loads((s/'input-pin.json').read_text());raw=Path(ip['path']).read_bytes();assert hashlib.sha256(raw).hexdigest()==ip['sha256']
data=list(map(int,raw.split()));allowed=data[:1296];pos=1296
mask=[]
for e in range(10):
 row=[]
 for k in range(1296):
  row.append(sum(data[pos+j]<<(64*j) for j in range(4)));pos+=4
 mask.append(row)
coords=[]
for u in range(5):
 row=[]
 for a in range(3):row.append(sum(data[pos+j]<<(64*j) for j in range(4)));pos+=4
 coords.append(row)
assert pos==len(data)
ps=list(itertools.permutations(range(3)));edges=list(itertools.combinations(range(5),2));lookup={p:i for i,p in enumerate(ps)};counts=[]
for line in (s/'orbits.jsonl').read_text().splitlines():
 r=json.loads(line);code=r['representative_code'];digits=[]
 for _ in range(10):digits.append(code%6);code//=6
 digits=digits[::-1];P={};h=[[0]*3 for _ in range(5)]
 for (u,v),d in zip(edges,digits):
  perm=ps[d];inv=tuple(perm.index(a) for a in range(3));P[u,v]=perm;P[v,u]=inv;h[u][inv[0]]+=1;h[v][perm[0]]+=1
 assert all(row[0]<=2 and row[1]<=3 and row[2]<=3 for row in h)
 bits=(1<<243)-1
 for e,(u,v) in enumerate(edges):
  key=lookup[P[u,v]]
  for w in range(5):
   if w!=u and w!=v:key=6*key+lookup[tuple(P[w,v][P[u,w][a]] for a in range(3))]
  assert allowed[key];bits &=mask[e][key]
 assert bits.bit_count()>=10
 assert all((bits&coords[u][a]).bit_count()>=(4 if a==0 else 3) for u in range(5) for a in range(3))
 counts.append(bits.bit_count())
print(json.dumps({'representatives_valid':len(counts),'min_word_support':min(counts),'max_word_support':max(counts)}))
