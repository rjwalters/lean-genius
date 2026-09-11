import pathlib,json,time,itertools
out=pathlib.Path(__file__).parent;base=out.parent;cross=json.loads((base/'n78-five-orbit-single-cross/results.json').read_text());first=json.loads((base/'n78-five-orbit-single-residual/results.json').read_text());par=pathlib.Path('/tmp/erdos85-sol1-q9-n78-four-orbit-order24-parameters')
groups=json.loads((par/'groups.json').read_text());params=json.loads((par/'results.json').read_text())['records']
roots=[(i,j,sol) for i,r in enumerate(first['records']) for j,sol in enumerate(r['survivors'])];start=time.monotonic();records=[];cache={};expired=False
def guard():
    if time.monotonic()-start>30:raise TimeoutError
try:
    for fi,bi,bsol in roots:
        guard();fr=first['records'][fi];r=cross['records'][fr['root']];cfg=r['survivors'][fr['configuration']];gi,ai=r['group'],r['action'];m=groups[gi]['multiplication'];act=params[gi]['actions'][ai];labels=act['labels']
        if (gi,ai) not in cache:
            cache[gi,ai]=[(l,sorted({tuple(sorted((x,m[l][x]))) for x in range(24)})) for l in range(1,24) if m[l][l]==0 and all(labels[m[l][x]]!=labels[x] for x in act['coset_representatives'])]
        adj=[set() for _ in range(66)]
        def edge(a,b):adj[a].add(b);adj[b].add(a)
        for f in range(6):edge(f,act['matching'][f])
        for a in range(24):
            edge(labels[a],6+a);edge(labels[a],30+a)
            for s in cfg['U']:edge(6+a,6+m[a][s])
            for s in cfg['V']:edge(30+a,30+m[a][s])
            for s in cfg['T']:edge(6+a,30+m[a][s])
        neighborhoods=sorted({tuple(sorted([6+m[a][u] for u in bsol['U']]+[30+m[a][v] for v in bsol['V']])) for a in range(24)});assert len(neighborhoods)==12
        for j,ns in enumerate(neighborhoods):
            for v in ns:edge(54+j,v)
        masks=[sum(1<<x for x in row) for row in adj]
        rec={'first_record':fi,'first_solution':bi,'status':'RUNNING','candidate_neighborhoods':0,'survivors':[]};records.append(rec)
        for l,pairs in cache[gi,ai]:
            v=(0,l)
            if masks[30]&masks[30+l]:continue
            wanted=set(range(6))-{labels[0],labels[l]};possible=[]
            for pair in pairs:
                labs={labels[x] for x in pair}
                if len(labs)!=2 or not labs<=wanted:continue
                if any(masks[30+a]&masks[6+b] for a in v for b in pair):continue
                if masks[6+pair[0]]&masks[6+pair[1]]:continue
                possible.append((pair,labs))
            for (p,pl),(q,ql) in itertools.combinations(possible,2):
                if pl|ql!=wanted or pl&ql:continue
                if any(masks[6+a]&masks[6+b] for a in p for b in q):continue
                rec['candidate_neighborhoods']+=1;u=tuple(sorted(p+q));us=set(u);vs=set(v)
                if any(len(us&{m[g][a] for a in u})+len(vs&{m[g][a] for a in v})>1 for g in range(24) if g not in (0,l)):continue
                rec['survivors'].append({'l':l,'U':u,'V':v})
        rec['status']='COMPLETE'
except TimeoutError:
    expired=True
    if records and records[-1]['status']=='RUNNING':records[-1]['status']='UNKNOWN'
    for fi,bi,bsol in roots[len(records):]:records.append({'first_record':fi,'first_solution':bi,'status':'UNVISITED'})
result={'status':'UNKNOWN' if expired else 'COMPLETE','original_cap_seconds':30,'seconds':time.monotonic()-start,'roots':len(roots),'records':records}
(out/'results.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'status':result['status'],'seconds':result['seconds'],'roots':len(roots),'positive_roots':sum(bool(r.get('survivors')) for r in records),'survivors':sum(len(r.get('survivors',[])) for r in records)}))
