import pathlib,json,hashlib,itertools,time,sqlite3
out=pathlib.Path(__file__).parent;src=pathlib.Path('/tmp/erdos85-sol1-q9-n78-four-orbit-cross')
start=time.monotonic();done=[]
def guard():
    if time.monotonic()-start>30:
        (out/'audit.json').write_text(json.dumps({'status':'UNKNOWN','original_cap_seconds':30,'completed_roots':done}))
        raise SystemExit('original cap reached')
for name in ['pins.json','input-pins.json']:
    for f,h in json.loads((src/name).read_text()).items():
        p=pathlib.Path(f);p=p if p.is_absolute() else src/p
        assert hashlib.sha256(p.read_bytes()).hexdigest()==h
par=pathlib.Path('/tmp/erdos85-sol1-q9-n78-four-orbit-order24-parameters')
groups=json.loads((par/'groups.json').read_text());actions=json.loads((par/'results.json').read_text())['records']
records=json.loads((src/'results.json').read_text())['records']
witnesses={(r['root'],r['configuration']):r['neighbors'] for r in json.loads((src/'witnesses.json').read_text())}
c=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True)
for rid in [2314,2319,2322]:
    status,res=c.execute('select status,resolution from review_requests where id=?',(rid,)).fetchone()
    assert status=='resolved' and res.startswith('PASS')
assert [(r['group'],r['action'],r['a']) for r in records]==[(i,j,a) for i,r in enumerate(actions) for j in range(len(r['actions'])) for a in [1,4]]
internal_cache={};total_cross=0;direct_count=0;positive=0
def key(u,v,t):return tuple(sorted(u)),tuple(sorted(v)),tuple(sorted(t))
for root in records:
    guard();gi,ai,a=root['group'],root['action'],root['a'];g=groups[gi];m=g['multiplication'];inv=g['inverse']
    act=actions[gi]['actions'][ai];labels=act['labels'];allowed=set(range(6))-{act['partner']}
    if (gi,a) not in internal_cache:
        io=sorted({tuple(sorted({i,inv[i]})) for i in range(1,24)})
        sets=[]
        for n in range(1,a+1):
            for blocks in itertools.combinations(io,n):
                if sum(map(len,blocks))==a:sets.append(tuple(sorted(x for b in blocks for x in b)))
        internal_cache[gi,a]=sets
    good=[];bylabels={}
    for s in internal_cache[gi,a]:
        labs=frozenset(labels[x] for x in s)
        if len(labs)!=a or not labs<=allowed:continue
        ss=set(s)
        if any(len(ss&{m[h][x] for x in s})+int(labels[h]==0)>1 for h in range(1,24)):continue
        good.append(s);bylabels.setdefault(labs,[]).append(s)
    assert len(good)==root['internal_sets']
    found={};visited=0
    for u in good:
        ulabs={labels[x] for x in u};us=set(u)
        fibers=[[x for x in range(24) if labels[x]==l] for l in sorted(allowed-ulabs)]
        budget=[1-int(labels[h]==0)-len(us&{m[h][x] for x in u}) for h in range(24)]
        for t in itertools.product(*fibers):
            visited+=1
            if visited%512==0:guard()
            ti=tuple(inv[x] for x in t);tlabs=frozenset(labels[x] for x in ti)
            if len(tlabs)!=len(ti) or not tlabs<=allowed:continue
            vs=bylabels.get(frozenset(allowed-tlabs),[])
            if not vs:continue
            ts=set(t)
            if any(len(ts&{m[h][x] for x in t})>budget[h] for h in range(1,24)):continue
            for v in vs:
                direct_count+=1
                adj=[set() for _ in range(54)]
                def edge(x,y):adj[x].add(y);adj[y].add(x)
                for f in range(6):edge(f,act['matching'][f])
                for h in range(24):
                    edge(labels[h],6+h);edge(labels[h],30+h)
                    for s in u:edge(6+h,6+m[h][s])
                    for s in v:edge(30+h,30+m[h][s])
                    for s in t:edge(6+h,30+m[h][s])
                masks=[sum(1<<x for x in row) for row in adj]
                if any((masks[x]&masks[y]).bit_count()>1 for x,y in itertools.combinations(range(54),2)):continue
                assert [len(row) for row in adj]==[9]*6+[6]*48
                assert all(i not in row for i,row in enumerate(adj))
                found[key(u,v,t)]=[sorted(row) for row in adj]
    saved={key(s['U'],s['V'],s['T']) for s in root['survivors']}
    assert found.keys()==saved
    for j,s in enumerate(root['survivors']):assert found[key(s['U'],s['V'],s['T'])]==witnesses[root['index'],j]
    assert visited==root['cross_choices_visited']
    total_cross+=visited;positive+=len(found);done.append(root['index'])
guard()
result={'status':'COMPLETE','original_cap_seconds':30,'seconds':time.monotonic()-start,'roots':len(done),'cross_choices':total_cross,'direct_graph_candidates':direct_count,'positive_graphs':positive,'exact_saved_graphs_match':True}
(out/'audit.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
