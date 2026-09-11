import itertools,json,pathlib,time
out=pathlib.Path(__file__).parent
par=pathlib.Path('/tmp/erdos85-sol1-q9-n78-four-orbit-order24-parameters')
groups=json.loads((par/'groups.json').read_text());cubic=json.loads((par/'results.json').read_text())['records']
start=time.monotonic();records=[];contexts=[];expired=False
def guard():
    if time.monotonic()-start>30:raise TimeoutError
def closure(m,seed):
    h=set(seed)|{0}
    while len(h)<=8:
        new=h|{m[a][b] for a in h for b in h}
        if new==h:return frozenset(h)
        h=new
    return None
def mask(s):return sum(1<<x for x in s)
try:
    for gi,g in enumerate(groups):
        guard()
        if not cubic[gi]['cubic_sets']:continue
        m=g['multiplication'];seen={frozenset({0})};todo=list(seen)
        while todo:
            h=todo.pop()
            if len(h)==8:continue
            for x in range(24):
                guard();new=closure(m,h|{x})
                if new is not None and new not in seen:seen.add(new);todo.append(new)
        for h in sorted((tuple(sorted(h)) for h in seen if len(h)==8)):
            cosets=sorted({tuple(sorted(m[a][x] for x in h)) for a in range(24)},key=min)
            assert len(cosets)==3
            labels=[next(i for i,c in enumerate(cosets) if a in c) for a in range(24)]
            contexts.append({'group':gi,'H':h,'cosets':cosets,'labels':labels})
    for ci,ctx in enumerate(contexts):
        guard();gi=ctx['group'];g=groups[gi];m=g['multiplication'];inv=g['inverse'];labels=ctx['labels']
        rec={'context':ci,'status':'RUNNING','internal_sets':[],'cross_sets':0,'tested_triples':0,'survivors':[]};records.append(rec)
        ss=[]
        for s in cubic[gi]['cubic_sets']:
            if len({labels[x] for x in s})!=3:continue
            sm=mask(s);trans=[mask({m[a][x] for x in s}) for a in range(24)]
            if any((sm&trans[a]).bit_count()+int(labels[a]==0)>1 for a in range(1,24)):continue
            ss.append((tuple(s),sm,trans));rec['internal_sets'].append(s)
        for t in itertools.product(ctx['cosets'][1],ctx['cosets'][2]):
            guard();ti=tuple(inv[x] for x in t)
            if {labels[x] for x in ti}!={1,2}:continue
            rec['cross_sets']+=1
            tm=mask(t);tim=mask(ti)
            tt=[mask({m[a][x] for x in t}) for a in range(24)]
            tit=[mask({m[a][x] for x in ti}) for a in range(24)]
            us=[s for s in ss if all((s[1]&s[2][a]).bit_count()+(tm&tt[a]).bit_count()+int(labels[a]==0)<=1 for a in range(1,24))]
            vs=[s for s in ss if all((s[1]&s[2][a]).bit_count()+(tim&tit[a]).bit_count()+int(labels[a]==0)<=1 for a in range(1,24))]
            for u in us:
                for v in vs:
                    rec['tested_triples']+=1
                    if all((u[1]&tit[a]).bit_count()+(tm&v[2][a]).bit_count()<=1 for a in range(24)):
                        rec['survivors'].append({'U':u[0],'V':v[0],'T':t})
        rec['status']='COMPLETE'
except TimeoutError:
    expired=True
    if records and records[-1]['status']=='RUNNING':records[-1]['status']='UNKNOWN'
    for ci in range(len(records),len(contexts)):records.append({'context':ci,'status':'UNVISITED'})
result={'status':'UNKNOWN' if expired else 'COMPLETE','original_cap_seconds':30,'seconds':time.monotonic()-start,'context_enumeration_complete':len(records)>0,'contexts':contexts,'records':records}
(out/'results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':result['status'],'seconds':result['seconds'],'contexts':len(contexts),'positive_roots':sum(bool(r.get('survivors')) for r in records),'survivors':sum(len(r.get('survivors',[])) for r in records)}))
