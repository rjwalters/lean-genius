"""Necessary order-eight matrices in Z[x]/(x^4+1), no graph/SAT search."""
import collections,functools,itertools,json,math,time
from pathlib import Path
P=Path(__file__).resolve().parent;B=P.parent
assert not (P/'launch.json').exists()
(P/'launch.json').write_text(json.dumps({'cases':4,'max_operations_per_case':100000,'seconds':60,'scope':'necessary character matrices only'})+'\n')
started=time.monotonic();zero=(0,0,0,0);one=(1,0,0,0)
units=[tuple((1 if j==r else 0) for j in range(4)) for r in range(4)]
units+= [tuple(-x for x in u) for u in units]
def add(a,b):return tuple(x+y for x,y in zip(a,b))
def conj(a):return (a[0],-a[3],-a[2],-a[1])
@functools.lru_cache(None)
def mul(a,b):
    out=[0]*4
    for i,x in enumerate(a):
        for j,y in enumerate(b):out[(i+j)%4]+=(1 if i+j<4 else -1)*x*y
    return tuple(out)
def dot(a,b):
    out=zero
    for x,y in zip(a,b):out=add(out,mul(x,conj(y)))
    return out
cross=collections.defaultdict(set);edges=collections.defaultdict(set)
masks=[(1<<r)|(1<<(r+8)) for r in range(8)]
for mask in range(1<<16):
    counts=[(mask&m).bit_count() for m in masks];total=sum(counts)
    h=sum((1 if r%2==0 else -1)*counts[r] for r in range(8))
    c=(counts[0]+counts[4]-counts[2]-counts[6],counts[1]+counts[5]-counts[3]-counts[7])
    d=tuple(counts[r]-counts[r+4] for r in range(4))
    cross[(total,h,c)].add(d)
    if total<=3:edges[(total,h,c)].add(d)
selfs=collections.defaultdict(set)
u4=((1,0),(0,1),(-1,0),(0,-1))
for mask in range(128):
    ss=[s for s in range(1,8) if mask>>(s-1)&1]
    total=9+2*len(ss);h=9+2*sum((-1)**s for s in ss)
    c=(9+2*sum(u4[s%4][0] for s in ss),0);d=(9,0,0,0)
    for s in ss:d=add(d,add(units[s],units[-s%8]))
    selfs[(total,h,c)].add(d)
q=json.loads((B/'n80-m16-quotient/verification.json').read_text())['representatives'][1]['matrix']
cases=json.loads((B/'n80-m16-character-gauge/orbits.json').read_text());assert len(cases)==4
q2=[[sum(q[i][k]*q[j][k] for k in range(5)) for j in range(5)] for i in range(5)]
def cdot(a,b):return (sum(x[0]*y[0]+x[1]*y[1] for x,y in zip(a,b)),sum(x[1]*y[0]-x[0]*y[1] for x,y in zip(a,b)))
class Cap(Exception):pass
out=(P/'retained.jsonl').open('w');results=[]
for case in cases:
    if time.monotonic()-started>=60:break
    h=[case['H'][5*i:5*i+5] for i in range(5)];c=[list(map(tuple,case['C'][5*i:5*i+5])) for i in range(5)]
    h2=[[sum(h[i][k]*h[j][k] for k in range(5)) for j in range(5)] for i in range(5)]
    c2=[[cdot(c[i],c[j]) for j in range(5)] for i in range(5)]
    ops=[0];kept=[0];row_counts=[];halt=False
    def tick():
        ops[0]+=1
        if ops[0]>100000 or time.monotonic()-started>=60:raise Cap()
    try:
        rows=[]
        for i in range(5):
            domains=[]
            for j in range(5):
                if i!=j:domains.append(sorted(edges[(q[i][j],h[i][j],c[i][j])]))
                elif q[i][i]<2:domains.append((one if q[i][i]==1 else zero,))
                else:
                    allowed=set()
                    for s in range(1,8):
                        if 16//math.gcd(16,s)>=5 and 2*((-1)**s)==h[i][i] and (2*u4[s%4][0],0)==c[i][i]:allowed.add(add(units[s],units[-s%8]))
                    domains.append(sorted(allowed))
            rs=[]
            for row in itertools.product(*domains):
                tick()
                if dot(row,row) in selfs[(q2[i][i],h2[i][i],c2[i][i])]:rs.append(row)
            rows.append(rs);row_counts.append(len(rs))
        order=sorted(range(5),key=lambda i:(len(rows[i]),i));indices=[]
        for level,i in enumerate(order):
            table=collections.defaultdict(list)
            for row in rows[i]:table[tuple(row[j] for j in order[:level])].append(row)
            indices.append(table)
        def visit(chosen):
            tick();level=len(chosen)
            if level==5:
                kept[0]+=1;out.write(json.dumps({'case':case['id'],'matrix':[z for i in range(5) for z in chosen[i]]},separators=(',',':'))+'\n')
                if out.tell()>80000000:raise Cap()
                return
            i=order[level];key=tuple(conj(chosen[j][i]) for j in order[:level])
            for row in indices[level].get(key,[]):
                if all(dot(row,chosen[j]) in cross[(q2[i][j],h2[i][j],c2[i][j])] for j in order[:level]):visit({**chosen,i:row})
        visit({});status='COMPLETE'
    except Cap:status='UNKNOWN';halt=time.monotonic()-started>=60 or out.tell()>80000000
    results.append({'case':case['id'],'status':status,'operations':ops[0],'row_domains':row_counts,'retained':kept[0]})
    if halt:break
out.close()
result={'status':'COMPLETE' if len(results)==4 and all(r['status']=='COMPLETE' for r in results) else 'PARTIAL',
        'cases':results,'unvisited':4-len(results),'seconds':time.monotonic()-started,'scope':'necessary ring-valued matrices only; no graph/SAT/Lean result'}
(P/'results.json').write_text(json.dumps(result,indent=2)+'\n');print(result)
