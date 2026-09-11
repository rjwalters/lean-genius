from pathlib import Path
import hashlib,itertools,json,time
src=Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3/q9-order3-local-contingency')
for f,h in json.loads((src/'pins.json').read_text())['files'].items():
    assert hashlib.sha256((src/f).read_bytes()).hexdigest()==h
expected=json.loads((src/'results.json').read_text())
start=time.monotonic();margins=(4,3,3)
tables=[]
for a,b,c,d in itertools.product(range(5),range(4),range(4),range(4)):
    table=((a,b,4-a-b),(c,d,3-c-d),(4-a-c,3-b-d,a+b+c+d-4))
    if min(x for row in table for x in row)<0:continue
    assert tuple(map(sum,table))==margins
    assert tuple(sum(table[i][j] for i in range(3)) for j in range(3))==margins
    tables.append(table)
assert len(tables)==65
perms=list(itertools.permutations(range(3)))
assert perms==list(map(tuple,expected['permutations']))
matrices=[[[int(p[i]==j) for j in range(3)] for i in range(3)] for p in perms]
E=[[0,0,0],[0,0,1],[0,1,0]]
def mul(A,B):return [[sum(A[i][k]*B[k][j] for k in range(3)) for j in range(3)] for i in range(3)]
records=expected['records'];assert len(records)==1296
counts=[];rejected=0
for case,key in enumerate(itertools.product(range(6),repeat=4)):
    assert time.monotonic()-start<60
    P=matrices[key[0]];left=mul(E,P);right=mul(P,E)
    cap=[[3-left[i][j]-right[i][j]-sum(matrices[k][i][j] for k in key[1:])
          for j in range(3)] for i in range(3)]
    n=sum(all(t[i][j]<=cap[i][j] for i in range(3) for j in range(3)) for t in tables)
    rec=records[case];assert (rec['direct'],*rec['paths'])==key
    assert n==rec['allowed_tables']
    cert=rec['rejection']
    if n:
        assert cert is None
    else:
        rejected+=1
        if 'negative_capacity' in cert:
            i,j=cert['negative_capacity'];assert cap[i][j]<0
        else:
            mask=cert['rows'];assert 0<mask<8
            demand=sum(margins[i] for i in range(3) if mask>>i&1)
            capacity=sum(min(margins[j],sum(cap[i][j] for i in range(3) if mask>>i&1)) for j in range(3))
            assert (demand,capacity)==(cert['demand'],cert['capacity']) and demand>capacity
    counts.append(n)
assert rejected==292 and expected['rejected']==292 and expected['retained']==1004
assert expected['status']=='COMPLETE' and expected['cases']==1296 and expected['table_count']==65
assert expected['original_wall_cap_seconds']==60 and expected['elapsed_seconds']<60
out=dict(status='PASS_COMPLETE_LOCAL',cases=1296,tables=65,rejected=292,retained=1004,
         all_exact_table_counts_match=True,all_rejection_certificates_verified=True,seconds=time.monotonic()-start)
Path(__file__).with_name('results.json').write_text(json.dumps(out,indent=2)+'\n')
Path(__file__).with_name('allowed-counts.json').write_text(json.dumps(counts)+'\n')
print(out)
