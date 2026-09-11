"""Coupled parity/order-four necessary matrices. No graph or SAT search."""
import collections,functools,hashlib,itertools,json,time
from pathlib import Path
P=Path(__file__).resolve().parent;BASE=P.parent
assert not (P/'launch.json').exists(), 'preserve capped domain; no retry'
quotients=[r['matrix'] for r in json.loads((BASE/'n80-m16-quotient/verification.json').read_text())['representatives']]
inputs=[]
for index,line in enumerate((BASE/'n80-m16-parity/retained.jsonl').read_text().splitlines()):
    r=json.loads(line)
    if r['type'] in (0,1,3,4):inputs.append({'source_index':index,**r})
assert len(inputs)==180
(P/'inputs.json').write_text(json.dumps(inputs,indent=2)+'\n')
(P/'launch.json').write_text(json.dumps({'cases':180,'max_operations_per_case':100000,'seconds':60,'scope':'necessary character matrices only'})+'\n')
units=(1,1j,-1,-1j)
@functools.lru_cache(None)
def edge_domain(degree,parity):
    return tuple(sorted({sum(units[r] for r in rs) for rs in itertools.combinations_with_replacement(range(4),degree)
                         if sum((-1)**r for r in rs)==parity},key=lambda z:(z.real,z.imag)))
@functools.lru_cache(None)
def cross_square(total,parity):
    return {complex(a-c,b-d) for a,b,c,d in itertools.product(range(5),repeat=4)
            if a+b+c+d==total and a+c-b-d==parity}
@functools.lru_cache(None)
def self_square(total,parity):
    return {9+sum(2*units[r%4].real for r in selected)
            for selected in itertools.combinations(range(1,8),(total-9)//2)
            if 9+sum(2*((-1)**r) for r in selected)==parity}
class Cap(Exception):pass
started=time.monotonic();records=[];out=(P/'retained.jsonl').open('w');halt=False
for case in inputs:
    if time.monotonic()-started>=60:break
    q=quotients[case['type']];h=[case['matrix'][i*5:i*5+5] for i in range(5)]
    q2=[[sum(q[i][k]*q[k][j] for k in range(5)) for j in range(5)] for i in range(5)]
    h2=[[sum(h[i][k]*h[k][j] for k in range(5)) for j in range(5)] for i in range(5)]
    ops=[0];count=[0];row_counts=[]
    def tick():
        ops[0]+=1
        if ops[0]>100000 or time.monotonic()-started>=60:raise Cap()
    try:
        tables=[]
        for i in range(5):
            domains=[]
            for j in range(5):
                if i==j:domains.append(((-2 if h[i][i]==2 else 0),) if q[i][i]==2 else (q[i][i],))
                else:domains.append(edge_domain(q[i][j],h[i][j]))
            table=collections.defaultdict(list);norms=self_square(q2[i][i],h2[i][i])
            for row in itertools.product(*domains):
                tick()
                if sum(z.real*z.real+z.imag*z.imag for z in row) in norms:table[row[:i]].append(row)
            tables.append(table);row_counts.append(sum(map(len,table.values())))
        def visit(rows):
            tick();i=len(rows)
            if i==5:
                count[0]+=1
                out.write(json.dumps({'source_index':case['source_index'],'type':case['type'],
                                      'matrix':[[int(z.real),int(z.imag)] for row in rows for z in row]},separators=(',',':'))+'\n')
                if out.tell()>80000000:raise Cap()
                return
            for row in tables[i].get(tuple(complex(r[i]).conjugate() for r in rows),[]):
                if all(sum(row[k]*complex(old[k]).conjugate() for k in range(5)) in cross_square(q2[i][j],h2[i][j]) for j,old in enumerate(rows)):
                    visit(rows+[row])
        visit([]);status='COMPLETE'
    except Cap:
        status='UNKNOWN';halt=time.monotonic()-started>=60 or out.tell()>80000000
    records.append({'source_index':case['source_index'],'type':case['type'],'status':status,'operations':ops[0],
                    'row_domain_sizes':row_counts,'retained':count[0]})
    if halt:break
out.close()
result={'status':'COMPLETE' if len(records)==180 and all(r['status']=='COMPLETE' for r in records) else 'PARTIAL',
        'visited':len(records),'unvisited':len(inputs)-len(records),'unknown':[r['source_index'] for r in records if r['status']=='UNKNOWN'],
        'retained':sum(r['retained'] for r in records),'seconds':time.monotonic()-started,'cases':records,
        'scope':'necessary order-four matrices only; no graph/lift/CNF/SAT verdict'}
(P/'results.json').write_text(json.dumps(result,indent=2)+'\n')
print({k:v for k,v in result.items() if k!='cases'})
