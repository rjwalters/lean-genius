import hashlib,importlib.util,itertools,json,pathlib,random,sqlite3,sys,time
P=pathlib.Path(__file__).parent;A=pathlib.Path('/Users/rwalters/lean-genius-q7-outside-first-20260910/h7-singleton-host-row-shortcut');R=A.parent/'h7-singleton-complete-row-api'
for f,h in json.loads((A/'pins.json').read_text()).items():assert hashlib.sha256((A/f).read_bytes()).hexdigest()==h
sys.path.insert(0,str(A));import compact
spec=importlib.util.spec_from_file_location('author',A/'check.py');author=importlib.util.module_from_spec(spec);spec.loader.exec_module(author)
fixtures=json.loads((R/'fixtures.json').read_text())
for i in range(4):
    perm=list(range(7,49));random.Random(8590+i).shuffle(perm);perm=list(range(7))+perm
    g=[[] for _ in range(49)]
    for u,ns in enumerate(fixtures[i]):g[perm[u]]=[perm[v] for v in ns]
    fixtures.append(g)
start=time.monotonic();domains=rows=trials=zero_reuse=0
for index,adj in enumerate(fixtures):
    g=list(map(set,adj));H=set(range(7));sup=[ns&H for ns in g];E={u for u in range(7,49) if not sup[u]};S=[u for u in range(7,49) if len(sup[u])==1];PV=[u for u in range(7,49) if len(sup[u])==2]
    a,count=author.singleton_rows(adj);plan=compact.prepare(adj);host={v:sum(1<<e for e in g[v]&E) for v in PV};b=compact.evaluate(plan,host)
    assert a==b and count==126
    for u in S:
        found=set();need=7-len(g[u]);eligible=[v for v in PV if all(not (g[v]-{u})&(g[w]-{u}) for w in g[u])]
        for vs in itertools.combinations(eligible,need):
            trials+=1;assert time.monotonic()-start<60
            final=g[u]|set(vs)
            if any(len(final&g[h])!=1 for h in H):continue
            if any((g[v]-{u})&(g[w]-{u}) for v,w in itertools.combinations(vs,2)):continue
            found.add(sum(1<<v for v in vs))
            if sum(not host[v] for v in vs)>=2:zero_reuse+=1
        assert found==set(a[u]) and len(a[u])==len(found),(index,u)
        domains+=1;rows+=len(found)
assert zero_reuse>0
db=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True);db.row_factory=sqlite3.Row
r=dict(db.execute('select * from review_requests where id=2109').fetchone());assert r['status']=='resolved' and r['resolution'].startswith('PASS')
(P/'premise.json').write_text(json.dumps(r,indent=2)+'\n')
out=dict(status='PASS',fixtures=len(fixtures),domains=domains,rows=rows,subset_trials=trials,rows_reusing_zero_host=zero_reuse,seconds=time.monotonic()-start)
(P/'results.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
