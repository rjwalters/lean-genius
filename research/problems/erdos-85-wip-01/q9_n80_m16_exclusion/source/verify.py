"""Independent bounded coefficient-count oracle and cyclic-convolution arithmetic."""
import collections,functools,itertools,json,time
from pathlib import Path
P=Path(__file__).resolve().parent;B=P.parent
assert not (P/'verification.json').exists()
start=time.monotonic();zero=(0,0,0,0)
def reduce8(a):return tuple(a[r]-a[r+4] for r in range(4))
def roots(counts):
    return (sum(counts),sum((-1)**r*counts[r] for r in range(8)),
            (counts[0]+counts[4]-counts[2]-counts[6],counts[1]+counts[5]-counts[3]-counts[7]),reduce8(counts))
def conjugate(a):
    extended=a+(0,0,0,0);return reduce8(tuple(extended[-r%8] for r in range(8)))
@functools.lru_cache(None)
def product(a,b):
    aa=a+(0,0,0,0);bb=b+(0,0,0,0)
    return reduce8(tuple(sum(aa[j]*bb[(r-j)%8] for j in range(8)) for r in range(8)))
def inner(a,b):
    products=[product(x,conjugate(y)) for x,y in zip(a,b)]
    return tuple(sum(x[r] for x in products) for r in range(4))
cross=collections.defaultdict(set);edge=collections.defaultdict(set)
for counts in itertools.product(range(3),repeat=8):
    n,h,c,d=roots(counts);cross[(n,h,c)].add(d)
    if n<=3:edge[(n,h,c)].add(d)
selfs=collections.defaultdict(set)
for chosen in itertools.product((0,1),repeat=7):
    coefficients=[0]*16;coefficients[0]=9
    for r,b in enumerate(chosen,1):coefficients[r]=coefficients[16-r]=b
    counts=tuple(coefficients[r]+coefficients[r+8] for r in range(8))
    n,h,c,d=roots(counts);selfs[(n,h,c)].add(d)
internal=collections.defaultdict(set)
for shift in range(1,9):
    adj=[{(v+shift)%16,(v-shift)%16} for v in range(16)]
    if any(len(adj[u]&adj[v])>1 for u in range(16) for v in range(u)):continue
    offsets=adj[0];counts=tuple(sum(s%8==r for s in offsets) for r in range(8))
    n,h,c,d=roots(counts);internal[(n,h,c)].add(d)
internal[(0,0,(0,0))].add(zero)
q=json.loads((B/'n80-m16-quotient/verification.json').read_text())['representatives'][1]['matrix']
cases=json.loads((B/'n80-m16-character-gauge/orbits.json').read_text())
q2=[[sum(q[i][k]*q[j][k] for k in range(5)) for j in range(5)] for i in range(5)]
results=[]
for case in cases:
    h=[case['H'][5*i:5*i+5] for i in range(5)];c=[case['C'][5*i:5*i+5] for i in range(5)]
    h2=[[sum(h[i][k]*h[j][k] for k in range(5)) for j in range(5)] for i in range(5)]
    c2=[[ (sum(c[i][k][0]*c[j][k][0]+c[i][k][1]*c[j][k][1] for k in range(5)),
            sum(c[i][k][1]*c[j][k][0]-c[i][k][0]*c[j][k][1] for k in range(5))) for j in range(5)] for i in range(5)]
    rows=[];ops=[0]
    for i in range(5):
        domains=[sorted((internal if i==j else edge)[(q[i][j],h[i][j],tuple(c[i][j]))]) for j in range(5)]
        rs=[]
        for row in itertools.product(*domains):
            ops[0]+=1
            if inner(row,row) in selfs[(q2[i][i],h2[i][i],c2[i][i])]:rs.append(row)
        rows.append(rs)
    # Deliberately reverse producer's small-domain ordering.
    order=sorted(range(5),key=lambda i:(-len(rows[i]),-i));indices=[]
    for level,i in enumerate(order):
        table=collections.defaultdict(list)
        for row in rows[i]:table[tuple(row[j] for j in order[:level])].append(row)
        indices.append(table)
    count=[0]
    def visit(chosen):
        ops[0]+=1;assert ops[0]<=100000 and time.monotonic()-start<60
        level=len(chosen)
        if level==5:count[0]+=1;return
        i=order[level];key=tuple(conjugate(chosen[j][i]) for j in order[:level])
        for row in indices[level].get(key,[]):
            if all(inner(row,chosen[j]) in cross[(q2[i][j],h2[i][j],c2[i][j])] for j in order[:level]):visit({**chosen,i:row})
    visit({});assert count[0]==0
    results.append({'case':case['id'],'retained':count[0],'row_domains':list(map(len,rows)),'operations':ops[0]})
source=json.loads((P/'results.json').read_text());assert source['status']=='COMPLETE' and source['unvisited']==0
assert [r['row_domains'] for r in results]==[r['row_domains'] for r in source['cases']]
assert all(r['retained']==0 and r['status']=='COMPLETE' for r in source['cases'])
assert (P/'retained.jsonl').read_bytes()==b''
result={'status':'PASS','cases':results,'seconds':time.monotonic()-start,
        'scope':'independent coefficient-count domains and cyclic-convolution join; all four necessary character systems inconsistent'}
(P/'verification.json').write_text(json.dumps(result,indent=2)+'\n');print(result)
