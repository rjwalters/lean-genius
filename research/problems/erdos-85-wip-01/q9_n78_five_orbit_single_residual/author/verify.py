import pathlib,json,itertools,time,hashlib
out=pathlib.Path(__file__).parent;cross=json.loads((out.parent/'n78-five-orbit-single-cross/results.json').read_text());data=json.loads((out/'results.json').read_text());par=pathlib.Path('/tmp/erdos85-sol1-q9-n78-four-orbit-order24-parameters')
groups=json.loads((par/'groups.json').read_text());params=json.loads((par/'results.json').read_text())['records'];start=time.monotonic();count=0;digest=hashlib.sha256()
for r in data['records']:
    if not r['survivors']:continue
    root=cross['records'][r['root']];cfg=root['survivors'][r['configuration']];m=groups[root['group']]['multiplication'];act=params[root['group']]['actions'][root['action']];labels=act['labels']
    for sol in r['survivors']:
        adj=[set() for _ in range(66)]
        def edge(a,b):adj[a].add(b);adj[b].add(a)
        for f in range(6):edge(f,act['matching'][f])
        for a in range(24):
            edge(labels[a],6+a);edge(labels[a],30+a)
            for s in cfg['U']:edge(6+a,6+m[a][s])
            for s in cfg['V']:edge(30+a,30+m[a][s])
            for s in cfg['T']:edge(6+a,30+m[a][s])
        neighborhoods={tuple(sorted([6+m[a][u] for u in sol['U']]+[30+m[a][v] for v in sol['V']])) for a in range(24)}
        assert len(neighborhoods)==12
        for i,ns in enumerate(sorted(neighborhoods)):
            for v in ns:edge(54+i,v)
        assert [len(row) for row in adj]==[9]*6+[7]*24+[8]*24+[6]*12
        masks=[sum(1<<x for x in row) for row in adj]
        assert all((masks[a]&masks[b]).bit_count()<=1 for a,b in itertools.combinations(range(66),2))
        for mask in masks:digest.update(mask.to_bytes(9,'little'))
        count+=1
result={'status':'COMPLETE','seconds':time.monotonic()-start,'positive_orbit_incidence_graphs':count,'codegree_pairs':count*2145,'adjacency_stream_sha256':digest.hexdigest()}
(out/'verification.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
