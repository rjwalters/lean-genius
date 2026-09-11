import json,pathlib,itertools,time,hashlib
out=pathlib.Path(__file__).parent;start=time.monotonic()
data=json.loads((out/'results.json').read_text());assert data['status']=='COMPLETE'
groups=json.loads(pathlib.Path('/tmp/erdos85-sol1-q9-n78-four-orbit-order24-parameters/groups.json').read_text())
checked=0;pairs=0;digest=hashlib.sha256()
for rec in data['records']:
    ctx=data['contexts'][rec['context']];m=groups[ctx['group']]['multiplication'];labels=ctx['labels']
    for cfg in rec['survivors']:
        if time.monotonic()-start>30:
            (out/'verification.json').write_text(json.dumps({'status':'UNKNOWN','checked':checked,'original_cap_seconds':30}))
            raise SystemExit('verification cap reached')
        adj=[set() for _ in range(54)]
        def edge(a,b):adj[a].add(b);adj[b].add(a)
        for f in range(3):edge(f,3+f)
        for g in range(24):
            edge(labels[g],6+g);edge(3+labels[g],30+g)
            for s in cfg['U']:edge(6+g,6+m[g][s])
            for s in cfg['V']:edge(30+g,30+m[g][s])
            for s in cfg['T']:edge(6+g,30+m[g][s])
        assert [len(row) for row in adj]==[9]*6+[6]*48
        assert all(v not in row for v,row in enumerate(adj))
        masks=[sum(1<<x for x in row) for row in adj]
        assert all((masks[a]&masks[b]).bit_count()<=1 for a,b in itertools.combinations(range(54),2))
        for mask in masks:digest.update(mask.to_bytes(7,'little'))
        checked+=1;pairs+=1431
result={'status':'COMPLETE','original_cap_seconds':30,'seconds':time.monotonic()-start,'positive_graphs':checked,'codegree_pairs':pairs,'adjacency_stream_sha256':digest.hexdigest()}
(out/'verification.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
