import pathlib,json,time,itertools
out=pathlib.Path(__file__).parent;src=out.parent/'n78-five-orbit-split-cross'
data=json.loads((src/'results.json').read_text());assert data['status']=='COMPLETE'
groups=json.loads(pathlib.Path('/tmp/erdos85-sol1-q9-n78-four-orbit-order24-parameters/groups.json').read_text())
start=time.monotonic();records=[];nodes=0;expired=False
roots=[(r['context'],j,cfg) for r in data['records'] for j,cfg in enumerate(r['survivors'])]
def guard():
    if time.monotonic()-start>30:raise TimeoutError
try:
    for ci,j,cfg in roots:
        guard();ctx=data['contexts'][ci];g=groups[ctx['group']];m=g['multiplication'];inv=g['inverse'];labels=ctx['labels']
        adj=[set() for _ in range(54)]
        def edge(a,b):adj[a].add(b);adj[b].add(a)
        for f in range(3):edge(f,3+f)
        for a in range(24):
            edge(labels[a],6+a);edge(3+labels[a],30+a)
            for s in cfg['U']:edge(6+a,6+m[a][s])
            for s in cfg['V']:edge(30+a,30+m[a][s])
            for s in cfg['T']:edge(6+a,30+m[a][s])
        masks=[sum(1<<x for x in row) for row in adj]
        # Positions0..23 are U and24..47 are V; Uidentity is position0.
        domains=[[a for a in range(48) if (labels[a%24]+3*(a//24))==f and not(masks[6]&masks[6+a])] for f in range(1,6)]
        domains.sort(key=len)
        rec={'context':ci,'configuration':j,'status':'RUNNING','nodes':0,'survivors':[]};records.append(rec)
        def dfs(i,chosen,diffs):
            global nodes
            nodes+=1;rec['nodes']+=1
            if nodes%1024==0:guard()
            if i==len(domains):rec['survivors'].append(chosen.copy());return
            for b in domains[i]:
                if any(masks[6+a]&masks[6+b] for a in chosen):continue
                extra=set();good=True
                for a in chosen:
                    if a//24!=b//24:continue
                    for q in [m[a%24][inv[b%24]],m[b%24][inv[a%24]]]:
                        if q in diffs or q in extra:good=False;break
                        extra.add(q)
                    if not good:break
                if good:dfs(i+1,chosen+[b],diffs|extra)
        dfs(0,[0],set());rec['status']='COMPLETE'
except TimeoutError:
    expired=True
    if records and records[-1]['status']=='RUNNING':records[-1]['status']='UNKNOWN'
    for ci,j,cfg in roots[len(records):]:records.append({'context':ci,'configuration':j,'status':'UNVISITED'})
result={'status':'UNKNOWN' if expired else 'COMPLETE','original_cap_seconds':30,'seconds':time.monotonic()-start,'nodes':nodes,'roots':len(roots),'records':records}
(out/'results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':result['status'],'seconds':result['seconds'],'roots':len(roots),'nodes':nodes,'positive_roots':sum(bool(r.get('survivors')) for r in records),'survivors':sum(len(r.get('survivors',[])) for r in records)}))
