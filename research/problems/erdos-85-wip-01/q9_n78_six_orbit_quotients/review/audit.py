import pathlib,json,hashlib,itertools,time,sqlite3
out=pathlib.Path(__file__).parent;src=pathlib.Path('/tmp/erdos85-sol1-q9-n78-six-orbit-quotients');start=time.monotonic()
for name in ['pins.json','input-pins.json']:
    for f,h in json.loads((src/name).read_text()).items():
        q=pathlib.Path(f);q=q if q.is_absolute() else src/q
        assert hashlib.sha256(q.read_bytes()).hexdigest()==h
data=json.loads((src/'results.json').read_text());assert data['status']=='COMPLETE'
parts=[(m,s) for m in [16,24,48] for s in itertools.combinations_with_replacement([d for d in range(1,m+1) if m%d==0 and m//d<=8],6) if sum(s)==78]
assert parts==[(r['order'],tuple(r['sizes'])) for r in data['cases']]
def comps(total,length):
    if length==1:yield (total,);return
    for a in range(total+1):
        for rest in comps(total-a,length-1):yield (a,)+rest
report=[]
for source in data['cases']:
    n=source['sizes'];found=set();visited=0
    def dfs(rows):
        nonlocal_placeholder=None
        global visited
        visited+=1
        if time.monotonic()-start>30:
            (out/'audit.json').write_text(json.dumps({'status':'UNKNOWN','original_cap_seconds':30,'completed_cases':report}))
            raise SystemExit('original cap reached')
        i=len(rows)
        if i==6:found.add(tuple(rows));return
        prefix=[]
        for j in range(i):
            numer=n[j]*rows[j][i]
            if numer%n[i]:return
            prefix.append(numer//n[i])
        remaining=9-sum(prefix)
        if remaining<0:return
        for tail in comps(remaining,6-i):
            row=tuple(prefix)+tail
            if row[i]>=n[i] or n[i]*row[i]%2:continue
            if any(n[i]*row[j]%n[j] for j in range(i+1,6)):continue
            trial=rows+[row]
            if any(sum(n[t]*r[j]*(r[j]-1)//2 for t,r in enumerate(trial))>n[j]*(n[j]-1)//2 for j in range(6)):continue
            if any(sum(n[t]*r[j]*r[k] for t,r in enumerate(trial))>n[j]*n[k] for j,k in itertools.combinations(range(6),2)):continue
            dfs(trial)
    dfs([])
    expected={tuple(tuple(row) for row in mat) for mat in source['quotients']}
    assert found==expected
    even={q for q in found if all(n[i]*q[i][i]%2==0 for i in range(6))}
    report.append({'order':source['order'],'sizes':n,'raw_count':len(found),'parity_count':len(even),'row_recursion_nodes':visited})
c=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True)
for rid in [2207,2264,2314,2315,2332]:
    s,r=c.execute('select status,resolution from review_requests where id=?',(rid,)).fetchone();assert s=='resolved' and r.startswith('PASS')
result={'status':'COMPLETE','original_cap_seconds':30,'seconds':time.monotonic()-start,'cases':report}
(out/'audit.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
