"""Independent parity-row domain join; no import of native enumerator."""
import collections,itertools,json,time
from pathlib import Path
P=Path(__file__).resolve().parent
assert not (P/'verification.json').exists()
qs=[r['matrix'] for r in json.loads((P.parent/'n80-m16-quotient/verification.json').read_text())['representatives']]
native=collections.defaultdict(set)
for line in (P/'retained.jsonl').read_text().splitlines():
    r=json.loads(line);q=tuple(r['matrix']);assert q not in native[r['type']];native[r['type']].add(q)
start=time.monotonic();results=[]
for t,q in enumerate(qs):
    square=[[sum(q[i][k]*q[k][j] for k in range(5)) for j in range(5)] for i in range(5)]
    tables=[]
    for i in range(5):
        table=collections.defaultdict(list);domains=[]
        for j in range(5):
            domains.append(((-2,2) if q[i][i]==2 else (q[i][i],)) if i==j else range(-q[i][j],q[i][j]+1,2))
        count=(square[i][i]-9)//2
        # Enumerate actual symmetric offset subsets, rather than the native count formula.
        norms={9+sum(2*((-1)**r) for r in selected) for selected in itertools.combinations(range(1,8),count)}
        for row in itertools.product(*domains):
            if sum(x*x for x in row) in norms:table[row[:i]].append(row)
        tables.append(table)
    found=set();nodes=[0];maximum=0
    def visit(rows,counter):
        counter[0]+=1;nodes[0]+=1;assert counter[0]<=100000 and time.monotonic()-start<60
        i=len(rows)
        if i==5:found.add(tuple(x for row in rows for x in row));return
        for row in tables[i].get(tuple(r[i] for r in rows),[]):
            ok=True
            for j,old in enumerate(rows):
                value=sum(a*b for a,b in zip(row,old));total=square[i][j]
                # Actual possible choice of E even offsets and total-E odd offsets.
                allowed={2*even-total for even in range(9) if 0<=total-even<=8}
                if value not in allowed:ok=False;break
            if ok:visit(rows+[row],counter)
    for row in tables[0][()]:
        counter=[0];visit([row],counter);maximum=max(maximum,counter[0])
    assert found==native[t]
    results.append({'type':t,'status':'PASS','retained':len(found),'nodes':nodes[0],'max_case_nodes':maximum})
(P/'verification.json').write_text(json.dumps({'status':'PASS','types':results,'seconds':time.monotonic()-start,'scope':'independent parity row-domain join; necessary only, not graph lift or exclusion'},indent=2)+'\n')
print(results)
