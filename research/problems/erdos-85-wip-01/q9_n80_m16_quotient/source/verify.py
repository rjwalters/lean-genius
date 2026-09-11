"""Independent full-row compatibility join, not the cross-entry producer traversal."""
import collections,hashlib,itertools,json,time
from pathlib import Path
P=Path(__file__).resolve().parent
assert not (P/'verification.json').exists(), 'preserve original verification'
start=time.monotonic();tables=[]
for i in range(5):
    table=collections.defaultdict(list)
    for xs in itertools.product(range(5),repeat=4):
        d=9-sum(xs)
        if d not in (0,1,2) or d*d+sum(x*x for x in xs)>24:continue
        row=list(xs);row.insert(i,d);table[tuple(row[:i])].append(tuple(row))
    tables.append(table)
found=[];nodes=maximum=0
def visit(rows,counter):
    global nodes
    counter[0]+=1;nodes+=1
    assert counter[0]<=100000 and time.monotonic()-start<60
    i=len(rows)
    if i==5:
        if all(sum(rows[i][k]*rows[j][k] for k in range(5))<=16 for i in range(5) for j in range(i)):
            found.append(tuple(x for row in rows for x in row))
        return
    prefix=tuple(row[i] for row in rows)
    for row in tables[i].get(prefix,[]):
        if any(row[i]==rows[j][j]==1 and row[j] for j in range(i)):continue
        visit(rows+[row],counter)
for row in tables[0][()]:
    counter=[0];visit([row],counter);maximum=max(maximum,counter[0])
source=[tuple(json.loads(line)) for line in (P/'quotients.jsonl').read_text().splitlines()]
assert sorted(found)==sorted(source) and len(source)==len(set(source))==210
perms=list(itertools.permutations(range(5)))
def canonical(q):return min(tuple(q[5*p[i]+p[j]] for i in range(5) for j in range(5)) for p in perms)
classes=collections.Counter(map(canonical,found))
assert all(0<=q[i*5+i]<=2 and sum(q[5*i:5*i+5])==9 for q in found for i in range(5))
result={'status':'PASS','matrices':len(found),'classes':len(classes),'class_multiplicities':sorted(classes.values()),'nodes':nodes,'max_nodes_per_first_row':maximum,'seconds':time.monotonic()-start,
        'representatives':[{'matrix':[list(q[i*5:i*5+5]) for i in range(5)],'multiplicity':c} for q,c in sorted(classes.items())],
        'scope':'independent complete row-template join and symmetry quotient; not graph existence/exclusion'}
(P/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='representatives'}))
