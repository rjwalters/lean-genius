from pathlib import Path
import hashlib,itertools,json,time,collections
P=Path(__file__).resolve().parent;S=Path('/tmp/erdos85-sol1-q9-n80-m20-quotient')
pins=json.loads((S/'pins.json').read_text())
assert all(hashlib.sha256((S/f).read_bytes()).hexdigest()==h for f,h in pins.items())
start=time.monotonic();out=[];pairs=list(itertools.combinations(range(4),2))
# Each cross degree x satisfies x(x-1)<=19, so x<=4.
# Enumerate all six cross entries first; row sums force all diagonals.
for values in itertools.product(range(5),repeat=6):
    q=[[0]*4 for _ in range(4)]
    for (i,j),x in zip(pairs,values):q[i][j]=q[j][i]=x
    for i in range(4):q[i][i]=9-sum(q[i])
    if any(q[i][i] not in (0,1,2) for i in range(4)):continue
    if any(sum(q[i][k]*q[k][j] for k in range(4))>(28 if i==j else 20) for i in range(4) for j in range(4)):continue
    if any(q[i][i]==q[j][j]==1 and q[i][j] for i,j in pairs):continue
    out.append(tuple(map(tuple,q)))
source=json.loads((S/'results.json').read_text())
assert sorted(out)==sorted(tuple(map(tuple,q)) for q in source['quotients'])
def canonical(q):
    return min(tuple(q[p[i]][p[j]] for i in range(4) for j in range(4)) for p in itertools.permutations(range(4)))
counts=collections.Counter(map(canonical,out))
assert len(out)==10 and sorted(counts.values())==[1,3,6]
result={'status':'PASS','cross_tuples':5**6,'retained':len(out),'class_multiplicities':sorted(counts.values()),'seconds':time.monotonic()-start,'scope':'independent complete necessary quotient cover, no graph search or exclusion'}
(P/'results.json').write_text(json.dumps(result,indent=2)+'\n')
(P/'input-pins.json').write_text(json.dumps(pins,indent=2)+'\n');print(result)
