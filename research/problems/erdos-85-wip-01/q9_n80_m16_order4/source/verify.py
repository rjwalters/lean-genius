"""Independent actual-residue subset oracle, integer pairs, smallest-row-first join."""
import collections,functools,itertools,json,math,time
from pathlib import Path
P=Path(__file__).resolve().parent;B=P.parent
assert not (P/'verification.json').exists()
start=time.monotonic();units=((1,0),(0,1),(-1,0),(0,-1))
cross=collections.defaultdict(set)
for mask in range(1<<16):
    counts=[(mask & sum(1<<x for x in range(r,16,4))).bit_count() for r in range(4)]
    cross[(sum(counts),counts[0]+counts[2]-counts[1]-counts[3])].add((counts[0]-counts[2],counts[1]-counts[3]))
self_values=collections.defaultdict(set)
for mask in range(128):
    offsets=[r for r in range(1,8) if mask>>(r-1)&1]
    total=9+2*len(offsets);parity=9+2*sum((-1)**r for r in offsets)
    self_values[(total,parity)].add(9+2*sum(units[r%4][0] for r in offsets))
@functools.lru_cache(None)
def edges(degree,parity):
    return tuple(sorted({(sum(units[x%4][0] for x in xs),sum(units[x%4][1] for x in xs))
                         for xs in itertools.combinations(range(16),degree) if sum((-1)**x for x in xs)==parity}))
def conj(z):return (z[0],-z[1])
def dot(a,b):return (sum(x[0]*y[0]+x[1]*y[1] for x,y in zip(a,b)),sum(x[1]*y[0]-x[0]*y[1] for x,y in zip(a,b)))
qs=[r['matrix'] for r in json.loads((B/'n80-m16-quotient/verification.json').read_text())['representatives']]
original=[json.loads(line) for line in (B/'n80-m16-parity/retained.jsonl').read_text().splitlines()]
inputs=json.loads((P/'inputs.json').read_text())
assert inputs==[{'source_index':j,**r} for j,r in enumerate(original) if r['type'] in (0,1,3,4)]
expected=collections.defaultdict(set)
for line in (P/'retained.jsonl').read_text().splitlines():
    r=json.loads(line);c=tuple(map(tuple,r['matrix']));assert c not in expected[r['source_index']];expected[r['source_index']].add(c)
results=[]
for case in inputs:
    q=qs[case['type']];h=[case['matrix'][i*5:i*5+5] for i in range(5)]
    q2=[[sum(q[i][k]*q[j][k] for k in range(5)) for j in range(5)] for i in range(5)]
    h2=[[sum(h[i][k]*h[j][k] for k in range(5)) for j in range(5)] for i in range(5)]
    rows=[];ops=[0]
    for i in range(5):
        domains=[]
        for j in range(5):
            if i!=j:domains.append(edges(q[i][j],h[i][j]));continue
            if q[i][i]<2:domains.append(((q[i][i],0),));continue
            allowed=set()
            for s in range(1,8):
                if 16//math.gcd(16,s)<5:continue
                if 2*((-1)**s)==h[i][i]:allowed.add((2*units[s%4][0],0))
            domains.append(tuple(sorted(allowed)))
        rs=[]
        for row in itertools.product(*domains):
            ops[0]+=1
            if sum(a*a+b*b for a,b in row) in self_values[(q2[i][i],h2[i][i])]:rs.append(row)
        rows.append(rs)
    order=sorted(range(5),key=lambda i:(len(rows[i]),-i));indices=[]
    for level,i in enumerate(order):
        table=collections.defaultdict(list)
        for row in rows[i]:table[tuple(row[j] for j in order[:level])].append(row)
        indices.append(table)
    found=set()
    def visit(chosen):
        ops[0]+=1;assert ops[0]<=100000 and time.monotonic()-start<60
        level=len(chosen)
        if level==5:found.add(tuple(z for i in range(5) for z in chosen[i]));return
        i=order[level];key=tuple(conj(chosen[j][i]) for j in order[:level])
        for row in indices[level].get(key,[]):
            if all(dot(row,chosen[j]) in cross[(q2[i][j],h2[i][j])] for j in order[:level]):
                visit({**chosen,i:row})
    visit({})
    assert found==expected[case['source_index']],case['source_index']
    results.append({'source_index':case['source_index'],'type':case['type'],'retained':len(found),'operations':ops[0]})
source=json.loads((P/'results.json').read_text());assert source['status']=='COMPLETE' and source['visited']==180 and source['unknown']==[] and source['unvisited']==0
assert [r['retained'] for r in results]==[r['retained'] for r in source['cases']]
result={'status':'PASS','cases':180,'retained':sum(r['retained'] for r in results),'max_case_operations':max(r['operations'] for r in results),
        'seconds':time.monotonic()-start,'case_results':results,'scope':'actual subset coefficient oracle and independent integer-pair join; no graph/lift result'}
(P/'verification.json').write_text(json.dumps(result,indent=2)+'\n');print({k:v for k,v in result.items() if k!='case_results'})
