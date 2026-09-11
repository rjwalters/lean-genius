import pathlib,json,itertools,time
out=pathlib.Path(__file__).parent;par=pathlib.Path('/tmp/erdos85-sol1-q9-n78-four-orbit-order24-parameters')
groups=json.loads((par/'groups.json').read_text());params=json.loads((par/'results.json').read_text())['records']
start=time.monotonic();records=[];cache={};expired=False
roots=[(gi,ai,a) for gi,r in enumerate(params) for ai in range(len(r['actions'])) for a in [1,2,3,4]]
def guard():
    if time.monotonic()-start>30:raise TimeoutError
def mask(s):return sum(1<<x for x in s)
try:
    for gi,ai,a in roots:
        guard();g=groups[gi];m=g['multiplication'];inv=g['inverse'];act=params[gi]['actions'][ai];labels=act['labels'];allowed=set(range(6))-{act['partner']}
        rec={'group':gi,'action':ai,'a':a,'status':'RUNNING','internal_sets':[],'cross_choices':0,'couplings':0,'survivors':[]};records.append(rec)
        if (gi,a) not in cache:
            io=sorted({tuple(sorted({x,inv[x]})) for x in range(1,24)})
            sets=[]
            for k in range(1,a+1):
                for blocks in itertools.combinations(io,k):
                    if sum(map(len,blocks))!=a:continue
                    s=tuple(sorted(x for b in blocks for x in b));sm=mask(s);trans=[mask({m[h][x] for x in s}) for h in range(24)]
                    if all((sm&trans[h]).bit_count()<=1 for h in range(1,24)):sets.append((s,sm,trans))
            cache[gi,a]=sets
        ss=[];bylabels={}
        for s in cache[gi,a]:
            ls=frozenset(labels[x] for x in s[0])
            if len(ls)!=a or not ls<=allowed:continue
            if any((s[1]&s[2][h]).bit_count()+int(labels[h]==0)>1 for h in range(1,24)):continue
            ss.append(s);bylabels.setdefault(ls,[]).append(s);rec['internal_sets'].append(s[0])
        for u in ss:
            missing=sorted(allowed-{labels[x] for x in u[0]})
            fibers=[[x for x in range(24) if labels[x]==f] for f in missing]
            budget=[1-int(labels[h]==0)-(u[1]&u[2][h]).bit_count() for h in range(24)]
            for t in itertools.product(*fibers):
                rec['cross_choices']+=1
                if rec['cross_choices']%256==0:guard()
                ti=tuple(inv[x] for x in t);li=frozenset(labels[x] for x in ti)
                if len(li)!=len(ti) or not li<=allowed:continue
                vs=bylabels.get(frozenset(allowed-li),[])
                if not vs:continue
                tm=mask(t);tim=mask(ti);tt=[mask({m[h][x] for x in t}) for h in range(24)]
                if any((tm&tt[h]).bit_count()>budget[h] for h in range(1,24)):continue
                tit=[mask({m[h][x] for x in ti}) for h in range(24)]
                for v in vs:
                    rec['couplings']+=1
                    if any((v[1]&v[2][h]).bit_count()+(tim&tit[h]).bit_count()+int(labels[h]==0)>1 for h in range(1,24)):continue
                    if any((u[1]&tit[h]).bit_count()+(tm&v[2][h]).bit_count()+int(labels[h]==0)>1 for h in range(24)):continue
                    rec['survivors'].append({'U':u[0],'V':v[0],'T':t})
        rec['status']='COMPLETE'
except TimeoutError:
    expired=True
    if records and records[-1]['status']=='RUNNING':records[-1]['status']='UNKNOWN'
    for gi,ai,a in roots[len(records):]:records.append({'group':gi,'action':ai,'a':a,'status':'UNVISITED'})
result={'status':'UNKNOWN' if expired else 'COMPLETE','original_cap_seconds':30,'seconds':time.monotonic()-start,'roots':len(roots),'records':records}
(out/'results.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'status':result['status'],'seconds':result['seconds'],'roots':len(roots),'positive_roots':sum(bool(r.get('survivors')) for r in records),'survivors':sum(len(r.get('survivors',[])) for r in records)}))
