import pathlib,json,time,itertools
out=pathlib.Path(__file__).parent;src=out.parent/'n78-five-orbit-single-cross';par=pathlib.Path('/tmp/erdos85-sol1-q9-n78-four-orbit-order24-parameters')
data=json.loads((src/'results.json').read_text());assert data['status']=='COMPLETE'
groups=json.loads((par/'groups.json').read_text());params=json.loads((par/'results.json').read_text())['records']
roots=[(i,j,cfg) for i,r in enumerate(data['records']) for j,cfg in enumerate(r['survivors'])]
start=time.monotonic();records=[];cache={};expired=False
def guard():
    if time.monotonic()-start>30:raise TimeoutError
try:
    for ri,ci,cfg in roots:
        guard();r=data['records'][ri];gi,ai=r['group'],r['action'];m=groups[gi]['multiplication'];act=params[gi]['actions'][ai];labels=act['labels']
        if (gi,ai) not in cache:
            ls=[]
            for l in range(1,24):
                if m[l][l]!=0:continue
                if any(labels[m[l][x]]==labels[x] for x in act['coset_representatives']):continue
                pairs=sorted({tuple(sorted((x,m[l][x]))) for x in range(24)})
                ls.append((l,pairs))
            cache[gi,ai]=ls
        rec={'root':ri,'configuration':ci,'status':'RUNNING','involutions':0,'candidate_neighborhoods':0,'survivors':[]};records.append(rec)
        adj=[set() for _ in range(54)]
        def edge(a,b):adj[a].add(b);adj[b].add(a)
        for f in range(6):edge(f,act['matching'][f])
        for a in range(24):
            edge(labels[a],6+a);edge(labels[a],30+a)
            for s in cfg['U']:edge(6+a,6+m[a][s])
            for s in cfg['V']:edge(30+a,30+m[a][s])
            for s in cfg['T']:edge(6+a,30+m[a][s])
        masks=[sum(1<<x for x in row) for row in adj]
        for l,pairs in cache[gi,ai]:
            rec['involutions']+=1
            u=(0,l)
            if masks[6]&masks[6+l]:continue
            wanted=set(range(6))-{labels[0],labels[l]}
            possible=[]
            for pair in pairs:
                labs={labels[x] for x in pair}
                if len(labs)!=2 or not labs<=wanted:continue
                if any(masks[6+a]&masks[30+b] for a in u for b in pair):continue
                if masks[30+pair[0]]&masks[30+pair[1]]:continue
                possible.append((pair,labs))
            for (p,pl),(q,ql) in itertools.combinations(possible,2):
                if pl|ql!=wanted or pl&ql:continue
                if any(masks[30+a]&masks[30+b] for a in p for b in q):continue
                rec['candidate_neighborhoods']+=1;v=tuple(sorted(p+q));us=set(u);vs=set(v)
                if any(len(us&{m[g][a] for a in u})+len(vs&{m[g][a] for a in v})>1 for g in range(24) if g not in (0,l)):continue
                rec['survivors'].append({'l':l,'U':u,'V':v})
        rec['status']='COMPLETE'
except TimeoutError:
    expired=True
    if records and records[-1]['status']=='RUNNING':records[-1]['status']='UNKNOWN'
    for ri,ci,cfg in roots[len(records):]:records.append({'root':ri,'configuration':ci,'status':'UNVISITED'})
result={'status':'UNKNOWN' if expired else 'COMPLETE','original_cap_seconds':30,'seconds':time.monotonic()-start,'roots':len(roots),'records':records}
(out/'results.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'status':result['status'],'seconds':result['seconds'],'roots':len(roots),'positive_roots':sum(bool(r.get('survivors')) for r in records),'survivors':sum(len(r.get('survivors',[])) for r in records)}))
